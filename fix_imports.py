#!/usr/bin/env python3
"""Move import statements to the beginning of Lean 4 files."""

import re
import sys

def fix_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Find all import lines
    import_lines = []
    other_lines = []

    for line in content.split('\n'):
        if line.strip().startswith('import '):
            import_lines.append(line)
        else:
            other_lines.append(line)

    # Reconstruct file: imports first, then blank line, then rest
    if import_lines:
        new_content = '\n'.join(import_lines) + '\n\n' + '\n'.join(other_lines)
    else:
        new_content = '\n'.join(other_lines)

    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(new_content)

    print(f"Fixed {filepath}")

if __name__ == '__main__':
    files = [
        'pnp3/Complexity/ComplexityClasses.lean',
        'pnp3/Complexity/NP_Separation.lean',
        'pnp3/Complexity/PropSetBridge.lean',
        'pnp3/Complexity/PsubsetPpoly_Examples.lean',
    ]

    for filepath in files:
        try:
            fix_file(filepath)
        except Exception as e:
            print(f"Error fixing {filepath}: {e}")
