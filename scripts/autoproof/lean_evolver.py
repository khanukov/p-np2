#!/usr/bin/env python3
"""
lean_evolver.py
================

Точный автономный цикл для одного Lean-файла с незавершённым доказательством.

Сценарий:
- у вас большой Lean-проект;
- почти всё уже доказано;
- остался один файл (target_file), который надо итеративно довести до конца;
- на каждой итерации мы не "угадываем", а строго валидируем через Lean.

Критерии успеха (все обязательны):
1) target_file компилируется (`lake env lean <target_file>`);
2) в target_file нет `sorry` и `admit`;
3) target_file не вводит новые `axiom`/`constant` (настраивается);
4) указанные theorem_names проходят `#print axioms ...` как axiom-free;
5) (опционально, но по умолчанию включено) весь проект проходит `lake build`.

Скрипт специально написан без внешних Python-зависимостей (только stdlib),
чтобы его можно было безопасно переносить прямо в Lean-репозиторий.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import json
import os
import pathlib
import re
import shlex
import subprocess
import textwrap
import urllib.error
import urllib.request
from typing import Any


# ---------------------------------------------------------------------------
# Модели данных
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class EvolverConfig:
    """Конфигурация запуска."""

    project_root: str
    target_file: str
    theorem_names: list[str]

    # Ограничение числа итераций.
    max_iters: int = 40

    # Базовые команды Lean.
    lean_cmd: list[str] = dataclasses.field(default_factory=lambda: ["lake", "env", "lean"])
    lake_build_cmd: list[str] = dataclasses.field(default_factory=lambda: ["lake", "build"])

    # Строгость проверок.
    check_whole_project: bool = True
    forbid_axiom_keywords: bool = True

    # Настройки генератора кандидатов (LLM / внешний инструмент).
    proposer: dict[str, Any] = dataclasses.field(default_factory=dict)


@dataclasses.dataclass
class ProposalResult:
    """Кандидат следующей версии target_file."""

    content: str
    raw_payload: str
    proposer_name: str


@dataclasses.dataclass
class CheckResult:
    """
    Результат полной Lean-валидации одной итерации.

    Поле errors должно содержать максимально точную причину, почему неуспех.
    """

    solved: bool
    errors: list[str]
    compile_target_ok: bool
    build_project_ok: bool
    no_sorry_or_admit: bool
    no_axiom_keywords: bool
    axioms_ok: bool
    diagnostics: dict[str, str]


# ---------------------------------------------------------------------------
# Вспомогательные функции
# ---------------------------------------------------------------------------


def read_json(path: pathlib.Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def write_text(path: pathlib.Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def run_command(cmd: list[str], cwd: pathlib.Path, timeout_sec: int = 300) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        timeout=timeout_sec,
        check=False,
    )


def tail(text: str, limit: int = 8000) -> str:
    """Возвращает хвост строки для компактных логов."""
    return text[-limit:] if len(text) > limit else text


def lean_import_of_file(project_root: pathlib.Path, file_path: pathlib.Path) -> str:
    """Преобразование `<root>/A/B/C.lean` -> `A.B.C`."""
    rel = file_path.relative_to(project_root)
    if rel.suffix != ".lean":
        raise ValueError(f"target_file должен иметь расширение .lean: {file_path}")
    return ".".join(rel.with_suffix("").parts)


def strip_lean_comments(source: str) -> str:
    """
    Удаляет line/block комментарии Lean, включая вложенные /- ... -/.

    Это нужно, чтобы не ловить ложные срабатывания по `sorry`/`axiom` в комментариях.
    """
    out = []
    i = 0
    n = len(source)
    block_depth = 0
    while i < n:
        if block_depth == 0 and i + 1 < n and source[i] == '-' and source[i + 1] == '-':
            # line comment
            while i < n and source[i] != '\n':
                i += 1
            continue
        if i + 1 < n and source[i] == '/' and source[i + 1] == '-':
            block_depth += 1
            i += 2
            continue
        if block_depth > 0 and i + 1 < n and source[i] == '-' and source[i + 1] == '/':
            block_depth -= 1
            i += 2
            continue
        if block_depth == 0:
            out.append(source[i])
        i += 1
    return "".join(out)


def find_forbidden_tokens(source: str) -> dict[str, bool]:
    """Проверки на незавершённость и запрещённые конструкции в коде."""
    clean = strip_lean_comments(source)
    return {
        "has_sorry": re.search(r"\bsorry\b", clean) is not None,
        "has_admit": re.search(r"\badmit\b", clean) is not None,
        "has_axiom_decl": re.search(r"(?m)^\s*axiom\b", clean) is not None,
        "has_constant_decl": re.search(r"(?m)^\s*constant\b", clean) is not None,
    }


# ---------------------------------------------------------------------------
# Lean-валидация
# ---------------------------------------------------------------------------


class LeanVerifier:
    """Инкапсулирует все проверки Lean/файла на каждой итерации."""

    def __init__(self, cfg: EvolverConfig) -> None:
        self.cfg = cfg
        self.project_root = pathlib.Path(cfg.project_root).resolve()
        self.target_file = pathlib.Path(cfg.target_file).resolve()

    def check(self) -> CheckResult:
        errors: list[str] = []
        diagnostics: dict[str, str] = {}

        # 1) Компиляция target_file
        compile_proc = run_command([*self.cfg.lean_cmd, str(self.target_file)], cwd=self.project_root)
        compile_target_ok = compile_proc.returncode == 0
        diagnostics["compile_target_stdout"] = tail(compile_proc.stdout)
        diagnostics["compile_target_stderr"] = tail(compile_proc.stderr)
        if not compile_target_ok:
            errors.append("target_file не компилируется")

        # 2) Токены незавершённости / запрещённые декларации
        content = self.target_file.read_text(encoding="utf-8")
        flags = find_forbidden_tokens(content)

        no_sorry_or_admit = not (flags["has_sorry"] or flags["has_admit"])
        if not no_sorry_or_admit:
            if flags["has_sorry"]:
                errors.append("в target_file найден `sorry`")
            if flags["has_admit"]:
                errors.append("в target_file найден `admit`")

        no_axiom_keywords = True
        if self.cfg.forbid_axiom_keywords:
            no_axiom_keywords = not (flags["has_axiom_decl"] or flags["has_constant_decl"])
            if flags["has_axiom_decl"]:
                errors.append("в target_file найдена декларация `axiom`")
            if flags["has_constant_decl"]:
                errors.append("в target_file найдена декларация `constant`")

        # 3) Проверка axiom-free у целевых теорем
        axioms_ok, axiom_report = self._check_axioms_for_theorems()
        diagnostics["axiom_report"] = tail(axiom_report)
        if not axioms_ok:
            errors.append("`#print axioms` показывает зависимости от аксиом или не выполнен")

        # 4) Полная сборка проекта (опционально)
        build_project_ok = True
        if self.cfg.check_whole_project:
            build_proc = run_command(self.cfg.lake_build_cmd, cwd=self.project_root)
            build_project_ok = build_proc.returncode == 0
            diagnostics["lake_build_stdout"] = tail(build_proc.stdout)
            diagnostics["lake_build_stderr"] = tail(build_proc.stderr)
            if not build_project_ok:
                errors.append("`lake build` не проходит для проекта")

        solved = (
            compile_target_ok
            and no_sorry_or_admit
            and no_axiom_keywords
            and axioms_ok
            and build_project_ok
        )

        return CheckResult(
            solved=solved,
            errors=errors,
            compile_target_ok=compile_target_ok,
            build_project_ok=build_project_ok,
            no_sorry_or_admit=no_sorry_or_admit,
            no_axiom_keywords=no_axiom_keywords,
            axioms_ok=axioms_ok,
            diagnostics=diagnostics,
        )

    def _check_axioms_for_theorems(self) -> tuple[bool, str]:
        """Создаёт временный Lean-файл и запускает `#print axioms` для theorem_names."""
        import_name = lean_import_of_file(self.project_root, self.target_file)

        lines = [f"import {import_name}", ""]
        for theorem_name in self.cfg.theorem_names:
            lines.append(f"#print axioms {theorem_name}")

        check_file = self.project_root / ".autoproof_axiom_check.lean"
        write_text(check_file, "\n".join(lines) + "\n")

        try:
            proc = run_command([*self.cfg.lean_cmd, str(check_file)], cwd=self.project_root)
            report = (proc.stdout or "") + "\n" + (proc.stderr or "")

            markers = [f"{name} does not depend on any axioms" for name in self.cfg.theorem_names]
            ok = proc.returncode == 0 and all(marker in report for marker in markers)
            return ok, report
        finally:
            try:
                check_file.unlink(missing_ok=True)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Генератор кандидатов (proposer)
# ---------------------------------------------------------------------------


class BaseProposer:
    def propose(
        self,
        *,
        iteration: int,
        current_file_text: str,
        previous_check: CheckResult | None,
        prompt_path: pathlib.Path,
    ) -> ProposalResult:
        raise NotImplementedError


class CommandProposer(BaseProposer):
    """
    Универсальный proposer через внешнюю команду.

    Это самый переносимый режим для Lean-репозиториев:
    - можно подключить свой локальный LLM CLI;
    - можно подключить любой внутренний тул.

    config proposer mode=command:
      {
        "mode": "command",
        "cmd": "my_llm --prompt {prompt_path} --out {output_path}",
        "read": "output_file" | "stdout",
        "timeout_sec": 240
      }

    Подстановки:
      {prompt_path} - путь к prompt-файлу итерации
      {output_path} - путь, куда команда должна записать итоговый lean-файл
    """

    def __init__(self, cfg: EvolverConfig, run_dir: pathlib.Path) -> None:
        self.cfg = cfg
        self.run_dir = run_dir

        raw_cmd = cfg.proposer.get("cmd")
        if not raw_cmd:
            raise ValueError("Для proposer.mode=command нужно указать proposer.cmd")

        self.cmd_template = raw_cmd
        self.read_mode = cfg.proposer.get("read", "output_file")
        self.timeout_sec = int(cfg.proposer.get("timeout_sec", 240))

    def propose(
        self,
        *,
        iteration: int,
        current_file_text: str,
        previous_check: CheckResult | None,
        prompt_path: pathlib.Path,
    ) -> ProposalResult:
        output_path = self.run_dir / "iterations" / f"iter_{iteration:03d}_candidate_from_command.lean"
        cmd_str = self.cmd_template.format(prompt_path=str(prompt_path), output_path=str(output_path))

        proc = subprocess.run(
            cmd_str,
            cwd=str(pathlib.Path(self.cfg.project_root).resolve()),
            text=True,
            capture_output=True,
            timeout=self.timeout_sec,
            check=False,
            shell=True,
        )

        raw = json.dumps(
            {
                "command": cmd_str,
                "returncode": proc.returncode,
                "stdout": tail(proc.stdout, 12000),
                "stderr": tail(proc.stderr, 12000),
            },
            ensure_ascii=False,
            indent=2,
        )

        if proc.returncode != 0:
            raise RuntimeError(
                "Command proposer завершился с ошибкой. "
                f"returncode={proc.returncode}. См. raw_response.json"
            )

        if self.read_mode == "stdout":
            candidate = proc.stdout.strip()
        else:
            if not output_path.exists():
                raise RuntimeError(
                    f"Command proposer ожидал файл {output_path}, но его нет. "
                    "Проверьте proposer.cmd и proposer.read."
                )
            candidate = output_path.read_text(encoding="utf-8")

        if not candidate.strip():
            raise RuntimeError("Command proposer вернул пустой кандидат")

        return ProposalResult(content=candidate, raw_payload=raw, proposer_name="command")


class OpenAIProposer(BaseProposer):
    """
    OpenAI-compatible proposer без внешних библиотек.

    config proposer mode=openai:
      {
        "mode": "openai",
        "model": "gpt-4.1",
        "api_base": "https://api.openai.com/v1",
        "api_key_env": "OPENAI_API_KEY",
        "temperature": 0.1,
        "timeout_sec": 240
      }
    """

    def __init__(self, cfg: EvolverConfig) -> None:
        self.cfg = cfg
        p = cfg.proposer
        self.model = p.get("model", "gpt-4.1")
        self.api_base = p.get("api_base", "https://api.openai.com/v1").rstrip("/")
        self.api_key_env = p.get("api_key_env", "OPENAI_API_KEY")
        self.temperature = float(p.get("temperature", 0.1))
        self.timeout_sec = int(p.get("timeout_sec", 240))

        api_key = os.environ.get(self.api_key_env)
        if not api_key:
            raise RuntimeError(f"Не задан env {self.api_key_env} для OpenAI proposer")
        self.api_key = api_key

    def propose(
        self,
        *,
        iteration: int,
        current_file_text: str,
        previous_check: CheckResult | None,
        prompt_path: pathlib.Path,
    ) -> ProposalResult:
        prompt = prompt_path.read_text(encoding="utf-8")
        payload = {
            "model": self.model,
            "temperature": self.temperature,
            "messages": [
                {
                    "role": "system",
                    "content": (
                        "You are a Lean 4 theorem proving assistant. "
                        "Return only full Lean file content, no markdown."
                    ),
                },
                {"role": "user", "content": prompt},
            ],
        }

        body = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            url=f"{self.api_base}/chat/completions",
            data=body,
            method="POST",
            headers={
                "Authorization": f"Bearer {self.api_key}",
                "Content-Type": "application/json",
            },
        )

        try:
            with urllib.request.urlopen(req, timeout=self.timeout_sec) as resp:
                raw_bytes = resp.read()
        except urllib.error.HTTPError as e:
            details = e.read().decode("utf-8", errors="replace") if hasattr(e, "read") else str(e)
            raise RuntimeError(f"HTTP ошибка OpenAI proposer: {e.code}. {details}") from e
        except urllib.error.URLError as e:
            raise RuntimeError(f"Сетевая ошибка OpenAI proposer: {e}") from e

        raw_text = raw_bytes.decode("utf-8", errors="replace")
        try:
            data = json.loads(raw_text)
            content = data["choices"][0]["message"]["content"]
        except Exception as e:  # noqa: BLE001 - хотим детальную причину парсинга
            raise RuntimeError(
                "Не удалось распарсить ответ OpenAI proposer. "
                f"Сырой ответ: {tail(raw_text, 2000)}"
            ) from e

        candidate = content.strip()
        if not candidate:
            raise RuntimeError("OpenAI proposer вернул пустой кандидат")

        return ProposalResult(content=candidate, raw_payload=raw_text, proposer_name="openai")


# ---------------------------------------------------------------------------
# Основной цикл эволюции
# ---------------------------------------------------------------------------


class LeanProofEvolver:
    """Управляет итерациями, логами, валидацией и конечным статусом."""

    def __init__(self, cfg: EvolverConfig) -> None:
        self.cfg = cfg
        self.project_root = pathlib.Path(cfg.project_root).resolve()
        self.target_file = pathlib.Path(cfg.target_file).resolve()

        if not self.target_file.exists():
            raise FileNotFoundError(f"Не найден target_file: {self.target_file}")

        # Отдельный каталог артефактов каждой сессии.
        run_id = dt.datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        self.run_dir = self.project_root / ".autoproof_runs" / run_id
        self.iter_dir = self.run_dir / "iterations"
        self.iter_dir.mkdir(parents=True, exist_ok=True)

        self.verifier = LeanVerifier(cfg)
        self.proposer = self._build_proposer()

    def _build_proposer(self) -> BaseProposer:
        mode = (self.cfg.proposer.get("mode") or "command").lower()
        if mode == "command":
            return CommandProposer(self.cfg, self.run_dir)
        if mode == "openai":
            return OpenAIProposer(self.cfg)
        raise ValueError(f"Неизвестный proposer.mode: {mode}")

    def _build_prompt(self, iteration: int, current_text: str, previous_check: CheckResult | None) -> str:
        """Формирует очень подробный prompt с Lean-диагностикой."""
        if previous_check is None:
            status = "Это первая итерация. Нужен корректный полный Lean-файл без sorry/admit и без аксиом."
            errors = "(ещё нет)"
            diag = "(ещё нет)"
        else:
            status = f"solved={previous_check.solved}"
            errors = "\n".join(f"- {e}" for e in previous_check.errors) if previous_check.errors else "- ошибок нет"
            diag = json.dumps(previous_check.diagnostics, ensure_ascii=False, indent=2)

        return textwrap.dedent(
            f"""
            Ты решаешь Lean-задачу в одном файле.
            Верни ТОЛЬКО полный текст обновлённого Lean-файла (без markdown).

            Итерация: {iteration}
            Текущий статус: {status}

            Ошибки прошлого шага:
            {errors}

            Диагностика Lean (хвосты логов):
            {diag}

            Критерии успеха:
            1) target_file компилируется;
            2) нет sorry/admit;
            3) нет новых axiom/constant (если включено);
            4) theorem_names axiom-free по #print axioms;
            5) проект проходит lake build.

            Текущий файл:
            {current_text}
            """
        ).strip() + "\n"

    def run(self, restore_original_on_fail: bool) -> int:
        """Возвращает 0 при полном успехе, иначе 1."""
        original = self.target_file.read_text(encoding="utf-8")
        write_text(self.run_dir / "original_target.lean", original)
        write_text(self.run_dir / "config.json", json.dumps(dataclasses.asdict(self.cfg), ensure_ascii=False, indent=2))

        previous_check: CheckResult | None = None

        for i in range(1, self.cfg.max_iters + 1):
            current = self.target_file.read_text(encoding="utf-8")
            prompt = self._build_prompt(i, current, previous_check)
            prompt_path = self.iter_dir / f"iter_{i:03d}_prompt.txt"
            write_text(prompt_path, prompt)

            try:
                proposal = self.proposer.propose(
                    iteration=i,
                    current_file_text=current,
                    previous_check=previous_check,
                    prompt_path=prompt_path,
                )
            except Exception as e:  # noqa: BLE001
                # Если proposer сломался, фиксируем очень точную причину в артефакты.
                err = f"Ошибка proposer на итерации {i}: {type(e).__name__}: {e}"
                write_text(self.iter_dir / f"iter_{i:03d}_proposer_error.txt", err + "\n")
                write_text(self.run_dir / "FAILURE.txt", err + "\n")
                if restore_original_on_fail:
                    self.target_file.write_text(original, encoding="utf-8")
                print(err)
                return 1

            write_text(self.iter_dir / f"iter_{i:03d}_proposal_raw.txt", proposal.raw_payload)
            write_text(self.iter_dir / f"iter_{i:03d}_proposal.lean", proposal.content)

            # Применяем кандидата к target_file.
            candidate = proposal.content
            if not candidate.endswith("\n"):
                candidate += "\n"
            self.target_file.write_text(candidate, encoding="utf-8")

            # Верификация Lean.
            check = self.verifier.check()
            previous_check = check

            check_dump = {
                "iteration": i,
                "solved": check.solved,
                "errors": check.errors,
                "compile_target_ok": check.compile_target_ok,
                "build_project_ok": check.build_project_ok,
                "no_sorry_or_admit": check.no_sorry_or_admit,
                "no_axiom_keywords": check.no_axiom_keywords,
                "axioms_ok": check.axioms_ok,
                "diagnostics": check.diagnostics,
            }
            write_text(self.iter_dir / f"iter_{i:03d}_check.json", json.dumps(check_dump, ensure_ascii=False, indent=2))

            print(
                f"[iter {i:03d}] solved={check.solved} "
                f"compile={check.compile_target_ok} no_sorry={check.no_sorry_or_admit} "
                f"no_axiom_kw={check.no_axiom_keywords} axioms={check.axioms_ok} build={check.build_project_ok}"
            )

            if check.solved:
                write_text(self.run_dir / "SUCCESS.txt", f"Успех на итерации {i}.\n")
                return 0

        # Итер. лимит исчерпан.
        msg = (
            f"Достигнут max_iters={self.cfg.max_iters}, полное доказательство не закрыто.\n"
            "Смотрите последние iter_XXX_check.json и diagnostic хвосты логов.\n"
        )
        write_text(self.run_dir / "FAILURE.txt", msg)
        if restore_original_on_fail:
            self.target_file.write_text(original, encoding="utf-8")
        return 1


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Lean single-file proof evolver")
    parser.add_argument("--config", required=True, help="Путь к JSON-конфигу")
    parser.add_argument(
        "--restore-original-on-fail",
        action="store_true",
        help="Если не удалось закрыть доказательство, восстановить исходный target_file",
    )
    return parser.parse_args()


def load_config(path: pathlib.Path) -> EvolverConfig:
    raw = read_json(path)
    return EvolverConfig(
        project_root=raw["project_root"],
        target_file=raw["target_file"],
        theorem_names=list(raw["theorem_names"]),
        max_iters=int(raw.get("max_iters", 40)),
        lean_cmd=list(raw.get("lean_cmd", ["lake", "env", "lean"])),
        lake_build_cmd=list(raw.get("lake_build_cmd", ["lake", "build"])),
        check_whole_project=bool(raw.get("check_whole_project", True)),
        forbid_axiom_keywords=bool(raw.get("forbid_axiom_keywords", True)),
        proposer=dict(raw.get("proposer", {})),
    )


def main() -> int:
    args = parse_args()
    cfg = load_config(pathlib.Path(args.config).resolve())
    evolver = LeanProofEvolver(cfg)
    rc = evolver.run(restore_original_on_fail=args.restore_original_on_fail)

    if rc == 0:
        print("SUCCESS: файл и проект в полном порядке, теоремы axiom-free.")
    else:
        print("FAILURE: не удалось закрыть доказательство в пределах max_iters.")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
