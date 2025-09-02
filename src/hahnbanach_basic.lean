import Mathlib.Analysis.Normed.Space.HahnBanach.Extension
import Mathlib.Order.Zorn

-- Eを実ノルム空間、pをその部分空間、fをp上の連続線形汎関数とする
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (p : Subspace ℝ E) (f : p →L[ℝ] ℝ)

-- `f` の拡張を表現するための構造体を定義
-- `domain` は定義域となる部分空間
-- `toFun` は線形写像
-- `map_le` はノルムに関する条件
-- `mem_toFun` は `p` 上で `f` と一致することの証明
private structure Extension extends Subspace ℝ E where
  toFun : toFun →L[ℝ] ℝ
  map_le : ∀ x, toFun x ≤ ‖f‖ * ‖x‖
  mem_toFun : ∀ (x : p), toFun (x : E) = f x

-- 拡張の間の順序を定義
private instance : LE (Extension p f) :=
  ⟨fun g₁ g₂ => g₁.domain ≤ g₂.domain ∧ ∀ (x : g₁.domain), g₂.toFun x = g₁.toFun x⟩

-- この順序が半順序であることを示す
private instance : PartialOrder (Extension p f) where
  -- (省略)

-- ツォルンの補題を適用するために、鎖が上界を持つことを示す
private theorem zorn_extension : ∀ c : Set (Extension p f), IsChain (· ≤ ·) c → ∃ ub, ∀ z ∈ c, z ≤ ub := by
  intro c hchain
  -- 鎖 `c` に含まれるすべての拡張の定義域の合併をとる
  let s : Subspace ℝ E := ⨆ (g : c), g.1.val.domain
  -- 新しい拡張を構成する
  -- (中略: ここで、鎖の合併として定義される汎関数がwell-definedであること、
  --  線形性を持つこと、ノルム条件を満たすことなどが証明される)
  -- 構成した拡張が上界であることを示す
  -- (省略)

-- 主定理の証明
theorem Real.exists_extension_norm_eq' :
    ∃ (g : E →L[ℝ] ℝ), (∀ (x : p), g x = f x) ∧ ‖g‖ = ‖f‖ := by
  -- Zornの補題を用いて極大拡張 `g₀` を得る
  let ⟨g₀, h_max⟩ := zorn_of_chain_bounded (extension_chain_bounded p f)

  -- 極大拡張 `g₀` の定義域が `E` 全体であることを背理法で示す
  -- (中略: もしE全体でなければ、さらに1次元分拡張でき、g₀ の極大性に矛盾することを示す)

  -- 最終的に得られた線形写像 `g₀.toFun` が求める連続線形汎関数であることを示す
  -- (省略)
