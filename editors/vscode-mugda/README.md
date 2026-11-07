# Mugda Language Support for VS Code / VSCodium

This directory contains a lightweight VS Code / VSCodium extension providing syntax highlighting, comment toggling (`--` and `{- ... -}`), and bracket matching for Mugda (`.ma`) files.

## Features
- Highlights Mugda declaration keywords (`sized`, `data`, `codata`, `fun`, `cofun`, `mutual`, `let`, `in`, `eval`).
- Highlights built-in sorts (`Set`, `Size`), size operators (`$`, `#`), polarities (`+`, `-`), and dot patterns (`.x`, `.($ i)`).
- Supports line comments (`--`) and block comments (`{- ... -}`).

## Local Installation
Symlink or copy this folder into your VS Code extensions directory:

```bash
ln -s "$(pwd)/editors/vscode-mugda" ~/.vscode/extensions/vscode-mugda
```
