#!/usr/bin/env bash
# all_in_one_generator.sh — Lean4/Lake プロジェクト作成 & 実行
# 外部 Lean ファイルを取り込む --src / --as, mathlib 切替 -m/--mathlib

set -Eeuo pipefail

# ---- options -----------------------------------------------------------------
USE_MATHLIB="${USE_MATHLIB:-0}"
SRC=""
AS_MOD=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -m|--mathlib) USE_MATHLIB=1; shift ;;
    --src) SRC="${2:-}"; shift 2 ;;
    --as)  AS_MOD="${2:-}"; shift 2 ;;
    -h|--help)
      cat <<'USAGE'
Usage: ./all_in_one_generator.sh [-m|--mathlib] [--src FILE] [--as ModuleName] <project_name>

  -m, --mathlib     : mathlib を依存に追加（cache get も実行）
  --src FILE        : 外部 Lean ファイルをプロジェクトへ取り込み
  --as ModuleName   : 取り込み先モジュール名（既定: Math → Math.lean）
  <project_name>    : プロジェクト名（実行ターゲット名は正規化されます）
USAGE
      exit 0 ;;
    *) PROJ="${1}"; shift ;;
  esac
done

[[ -n "${PROJ:-}" ]] || { echo "ERROR: project_name を指定してください"; exit 1; }
command -v lake >/dev/null || { echo "ERROR: 'lake' が見つかりません（elan/lean/lake を導入）"; exit 1; }

# ---- name normalization ------------------------------------------------------
myproj="$PROJ"
# 実行/識別子に安全な形（英数_ のみ）。先頭が数字なら x を付与
exe="${myproj//[^A-Za-z0-9_]/_}"
[[ "$exe" =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]] || exe="x$exe"
# package は小文字
pkg_lower="$(echo "$exe" | tr '[:upper:]' '[:lower:]')"

# PascalCase 生成（lib 名/モジュール名用）
to_pascal() {
  local s="$1"; s="${s//-/_}"; s="${s// /_}"
  awk 'BEGIN{RS="_"; ORS=""} { if (length($0)) printf toupper(substr($0,1,1)) tolower(substr($0,2)); }' <<<"$s"
}
lib="$(to_pascal "$pkg_lower")"

# ---- project dir -------------------------------------------------------------
proj_dir="$pkg_lower"
mkdir -p "$proj_dir"
cd "$proj_dir"

echo "==> dir=$proj_dir  package=$pkg_lower  lib=$lib  exe=$exe"

# ---- decide source/destination module ---------------------------------------
root_mod="Main"        # 実行ルート（最終的に lakefile.lean の root へ）
wrapper_needed=0       # 外部ファイルに main が無い場合 wrapper(Main.lean) 生成
call_run_in_wrapper=0  # 外部に run があれば wrapper で呼ぶ

dst_mod=""             # 取り込み先モジュール名（= ファイル名ベース）

if [[ -n "$SRC" ]]; then
  [[ -f "$SRC" ]] || { echo "ERROR: --src '$SRC' が見つかりません"; exit 1; }
  # モジュール名の既定は Math（PascalCase 化）
  if [[ -n "$AS_MOD" ]]; then
    dst_mod="$(to_pascal "$AS_MOD")"
  else
    dst_mod="Math"
  fi
  cp "$SRC" "${dst_mod}.lean"

  # 外部が Mathlib を要求しているか自動検出（明示 -m が優先）
  if [[ "$USE_MATHLIB" = "0" ]] && grep -qE '^[[:space:]]*import[[:space:]]+Mathlib(\.|[[:space:]]|$)' "${dst_mod}.lean"; then
    USE_MATHLIB=1
    echo "   (detect) import Mathlib → mathlib を有効化します"
  fi

  # main/run の存在を検出
  if grep -qE '^[[:space:]]*def[[:space:]]+main\b' "${dst_mod}.lean"; then
    root_mod="$dst_mod"
    echo "   (detect) def main found in ${dst_mod}.lean → root := \`${root_mod}"
  else
    wrapper_needed=1
    root_mod="Main"
    if grep -qE '^[[:space:]]*def[[:space:]]+run\b' "${dst_mod}.lean"; then
      call_run_in_wrapper=1
      echo "   (detect) def run found in ${dst_mod}.lean → wrapper から呼び出します"
    else
      echo "   (note) main/run が見つからないため、wrapper Main.lean を生成します"
    fi
  fi
fi

# ---- lakefile.lean -----------------------------------------------------------
{
  echo "import Lake"
  echo "open Lake DSL"
  echo
  echo "package «$pkg_lower» where"
  echo
  echo "lean_lib «$lib» where"
  echo
  if [[ "$USE_MATHLIB" = "1" ]]; then
    echo 'require mathlib from git "https://github.com/leanprover-community/mathlib4.git"'
    echo
  fi
  echo "lean_exe $exe where"
  echo "  root := \`$root_mod"
} > lakefile.lean

# ---- Main.lean and/or default templates -------------------------------------
if [[ -n "$SRC" ]]; then
  if [[ "$wrapper_needed" = "1" ]]; then
    # wrapper Main.lean を生成して dst_mod を import
    if [[ "$call_run_in_wrapper" = "1" ]]; then
      cat > Main.lean <<EOF
import $dst_mod
def main : IO Unit := $dst_mod.run
EOF
    else
      cat > Main.lean <<EOF
import $dst_mod
def main : IO Unit := do
  IO.println "Imported $dst_mod (no 'main' or 'run' found)."
EOF
    fi
  fi
else
  # --src が無い場合：テンプレ生成
  if [[ "$USE_MATHLIB" = "1" ]]; then
    cat > Main.lean <<'EOF'
import Mathlib
open Nat
open scoped BigOperators

def main : IO Unit := do
  IO.println s!"fib 10 = {Nat.fib 10}"
  IO.println s!"fib 12 = {Nat.fib 12}"
EOF
  else
    cat > Main.lean <<EOF
def main : IO Unit := do
  IO.println "Hello from $exe"
EOF
  fi
fi

# ---- build & run -------------------------------------------------------------
echo "+ lake update"
lake update
if [[ "$USE_MATHLIB" = "1" ]]; then
  echo "+ lake exe cache get   # mathlib の olean キャッシュ取得（高速化）"
  lake exe cache get
fi
echo "+ lake build"
lake build
echo "+ lake exe $exe"
lake exe "$exe"

echo "BIN: ./build/bin/$exe"
