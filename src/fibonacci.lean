/-!
# Fibonacci と基本性質の証明（Lean 4 コアのみ）
このファイルでは自前で `fib` を定義し、いくつかの性質を証明します。
-/

namespace Fib

/-- フィボナッチ数の標準的定義：F₀=0, F₁=1, F_{n+2}=F_{n+1}+F_n -/
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n+2   => fib (n+1) + fib n

/-- 定義から直ちに得られる基本等式（`simp` で使えるように） -/
@[simp] lemma fib_zero : fib 0 = 0 := rfl
@[simp] lemma fib_one  : fib 1 = 1 := rfl
@[simp] lemma fib_succ_succ (n : Nat) : fib (n+2) = fib (n+1) + fib n := rfl

/-- 単調性：`fib n ≤ fib (n+1)` -/
theorem fib_le_succ (n : Nat) : fib n ≤ fib (n+1) := by
  induction n with
  | zero =>
      -- fib 0 = 0 ≤ 1 = fib 1
      simp
  | succ n ih =>
      -- 目標: fib (n+1) ≤ fib (n+2) = fib (n+1) + fib n
      -- 右辺は足し算で右に fib n を加えただけなので自明に ≥
      simpa [fib_succ_succ n] using Nat.le_add_right (fib (n+1)) (fib n)

/-- 正値性：全ての `n` で `fib (n+1) > 0` -/
theorem fib_pos_succ (n : Nat) : 0 < fib (n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- fib (n+2) = fib (n+1) + fib n ≥ fib (n+1) > 0
      have le_add : fib (n+1) ≤ fib (n+1) + fib n := Nat.le_add_right _ _
      have : 0 < fib (n+1) + fib n := Nat.lt_of_lt_of_le ih le_add
      simpa [fib_succ_succ n] using this

/-- 厳密単調性（1つ先）：全ての `n` で `fib (n+2) > fib (n+1)` は **成り立たない**（n=0 で等しい）ので、
    1 つずらして `fib (n+3) > fib (n+2)` を示す。 -/
theorem fib_strict_from0 (n : Nat) : fib (n+3) > fib (n+2) := by
  -- fib (n+3) = fib (n+2) + fib (n+1)、かつ fib (n+1) > 0 より直ちに従う
  have pos : 0 < fib (n+1) := fib_pos_succ n
  have : fib (n+2) < fib (n+2) + fib (n+1) := Nat.lt_add_of_pos_right _ pos
  simpa [fib_succ_succ (n+1)] using this

/-- `∑_{k=0}^{n} F_k + 1 = F_{n+2}` の形で総和公式を証明する。
    自然数の減法を避けるため、あえて `+1` 付きで述べる。 -/
def sumFib : Nat → Nat
  | 0     => 0
  | n+1   => sumFib n + fib (n+1)

@[simp] lemma sumFib_zero : sumFib 0 = 0 := rfl
@[simp] lemma sumFib_succ (n : Nat) : sumFib (n+1) = sumFib n + fib (n+1) := rfl

theorem sumFib_add_one_eq (n : Nat) : sumFib n + 1 = fib (n+2) := by
  induction n with
  | zero =>
      -- sumFib 0 + 1 = 0 + 1 = 1 = fib 2
      simp
  | succ n ih =>
      -- sumFib (n+1) + 1
      calc
        sumFib (n+1) + 1
            = (sumFib n + fib (n+1)) + 1 := by
                simp [sumFib_succ, Nat.add_assoc]
        _   = (sumFib n + 1) + fib (n+1) := by
                -- 和の並べ替え
                simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _   = fib (n+2) + fib (n+1) := by
                -- 帰納法の仮定を代入
                simpa [ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _   = fib (n+3) := by
                -- 定義より fib (n+3) = fib (n+2) + fib (n+1)
                simpa [fib_succ_succ (n+1)]

end Fib

/-- 実行：いくつか値を表示（証明自体はビルド成功で検証完了） -/
def main : IO Unit := do
  IO.println s!"fib 10 = {Fib.fib 10}"           -- 55
  IO.println s!"fib 11 = {Fib.fib 11}"           -- 89
  IO.println s!"sumFib 10 + 1 = {Fib.sumFib 10 + 1}"
  IO.println s!"fib 12 = {Fib.fib 12}"           -- = sumFib 10 + 1 のはず
