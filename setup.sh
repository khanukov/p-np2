#!/usr/bin/env bash
set -euo pipefail

echo "=== Настройка окружения для P≠NP проекта ==="

# Обновление пакетов
echo "Обновление системных пакетов..."
sudo apt-get update

# Установка elan (менеджер версий Lean)
echo "Установка elan..."
sudo apt-get install -y elan

# Установка нужной версии Lean toolchain
echo "Установка Lean toolchain из lean-toolchain..."
elan toolchain install $(cat lean-toolchain)

# Получение кэша зависимостей
echo "Получение кэша зависимостей..."
lake exe cache get

echo "=== Установка завершена! ==="
echo ""
echo "Теперь можно запустить:"
echo "  lake build        # Собрать проект"
echo "  lake test         # Запустить тесты"
