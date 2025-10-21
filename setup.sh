#!/usr/bin/env bash
set -euo pipefail

echo "=== Настройка окружения для P≠NP проекта ==="

# Проверка наличия elan
if command -v elan &> /dev/null; then
    echo "✓ elan уже установлен: $(elan --version)"
else
    echo "Установка elan..."
    # elan не доступен через apt, устанавливаем через официальный установщик
    if command -v curl &> /dev/null; then
        curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
        # Добавляем elan в PATH для текущей сессии
        export PATH="$HOME/.elan/bin:$PATH"
    else
        echo "❌ Ошибка: curl не найден. Установите curl и повторите попытку."
        exit 1
    fi
fi

# Проверка успешной установки elan
if ! command -v elan &> /dev/null; then
    echo "❌ Ошибка: elan не установлен. Возможны проблемы с сетевым подключением."
    echo ""
    echo "Альтернативный способ установки:"
    echo "  1. Установите elan вручную: https://github.com/leanprover/elan"
    echo "  2. Или используйте окружение с доступом к интернету"
    exit 1
fi

# Добавляем elan в PATH
export PATH="$HOME/.elan/bin:$PATH"

# Установка нужной версии Lean toolchain
echo "Установка Lean toolchain из lean-toolchain..."
elan toolchain install $(cat lean-toolchain)

# Проверка наличия lake
if ! command -v lake &> /dev/null; then
    echo "❌ Ошибка: lake не найден после установки toolchain"
    exit 1
fi

# Получение кэша зависимостей
echo "Получение кэша зависимостей..."
if ! lake exe cache get; then
    echo "⚠️  Предупреждение: не удалось получить кэш."
    echo "    Это может быть связано с проблемами сети."
    echo "    Вы можете собрать проект с нуля командой: lake build"
fi

echo ""
echo "=== Установка завершена! ==="
echo ""
echo "Добавьте elan в PATH для текущей сессии:"
echo '  export PATH="$HOME/.elan/bin:$PATH"'
echo ""
echo "Или добавьте в ~/.bashrc для постоянного использования:"
echo '  echo '\''export PATH="$HOME/.elan/bin:$PATH"'\'' >> ~/.bashrc'
echo ""
echo "Теперь можно запустить:"
echo "  lake build        # Собрать проект"
echo "  lake test         # Запустить тесты"
