# Lean AutoProof (single-target-file)

Этот скрипт предназначен для переноса в **основной Lean-репозиторий**.

## Что он делает

`lean_evolver.py` итеративно эволюционирует **один** целевой Lean-файл и после каждой итерации выполняет строгую проверку:

1. `lake env lean <target_file>` проходит;
2. в файле нет `sorry` и `admit`;
3. (по умолчанию) в файле нет деклараций `axiom`/`constant`;
4. указанные теоремы проходят `#print axioms` как axiom-free;
5. (по умолчанию) `lake build` проходит для всего проекта.

Если хоть один пункт не проходит, итерация считается неуспешной, а в артефакты пишется точная причина.

## Быстрый старт

1) Скопируйте `lean_evolver.py` и `lean_autoproof.example.json` в ваш Lean-проект.

2) Настройте `lean_autoproof.json` (или любое имя) под ваш проект:

- `project_root` — корень Lean-репозитория,
- `target_file` — ровно один файл с оставшимися proof obligations,
- `theorem_names` — теоремы, которые должны быть без аксиом,
- `proposer` — как получать следующую версию файла.

3) Запуск:

```bash
python lean_evolver.py --config lean_autoproof.json
```

Если хотите откатить файл при неуспехе:

```bash
python lean_evolver.py --config lean_autoproof.json --restore-original-on-fail
```

## Режимы proposer

### 1) Рекомендуется: `mode = "command"`

Скрипт вызывает внешний инструмент (например, ваш локальный LLM CLI):

```json
"proposer": {
  "mode": "command",
  "cmd": "my_llm_cli --prompt {prompt_path} --output {output_path}",
  "read": "output_file"
}
```

- `{prompt_path}` — путь к подробному prompt текущей итерации.
- `{output_path}` — куда инструмент должен записать полный `.lean` файл.

### 2) `mode = "openai"`

Есть встроенный OpenAI-compatible HTTP режим без внешних библиотек.

## Диагностика

Артефакты пишутся в `.autoproof_runs/<timestamp>/`:

- `original_target.lean` — исходная версия файла,
- `config.json` — зафиксированная конфигурация,
- `iterations/iter_XXX_prompt.txt` — prompt,
- `iterations/iter_XXX_proposal.lean` — предложенный файл,
- `iterations/iter_XXX_check.json` — точный результат проверок,
- `SUCCESS.txt` / `FAILURE.txt` — финальный статус.

Это сделано специально для максимально прозрачного дебага, если доказательство не закрывается.
