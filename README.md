# All-in-One lean4 project generator & build & runner

## Usage
```
Usage: ./all_in_one_generator.sh [-m|--mathlib] [--src FILE] [--as ModuleName] <project_name>

  -m, --mathlib     : mathlib を依存に追加（cache get も実行）
  --src FILE        : 外部 Lean ファイルをプロジェクトへ取り込み
  --as ModuleName   : 取り込み先モジュール名（既定: Math → Math.lean）
  <project_name>    : プロジェクト名（実行ターゲット名は正規化されます）

```
### Example
#without mathlib
> ./all_in_one_generator.sh proj  
#with mathlib
> ./all_in_one_generator.sh proj1_math -m  --SRC fibonacci.lean 

## Document (Japanese)
https://zenn.dev/xiangze/articles/24d33f3ebabfa0


