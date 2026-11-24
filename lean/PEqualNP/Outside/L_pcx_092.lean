import PEqualNP.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

theorem PEqualNP.Outside.L_pcx_092 : ∀ (n : ℕ) (B : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2)) (U : Submodule (ZMod 2) (Fin n → ZMod 2)), B.Nondegenerate → (∀ v, B v v = 0) → 2 * Module.finrank (ZMod 2) U ≤ n + (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (U ⊓ B.orthogonal U : Submodule (ZMod 2) (Fin n → ZMod 2))) := by
  intro n B U hB hAlt
  have hdimV : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by simp
  have horth : Module.finrank (ZMod 2) (B.orthogonal U) = n - Module.finrank (ZMod 2) U := by
    have h := LinearMap.BilinForm.finrank_orthogonal (B := B) hB U
    rw [hdimV] at h
    exact h
  have hle : Module.finrank (ZMod 2) (U ⊓ B.orthogonal U : Submodule (ZMod 2) (Fin n → ZMod 2)) ≤
      n - Module.finrank (ZMod 2) U := by
    refine le_trans (Submodule.finrank_mono inf_le_right) ?_
    rw [horth]
  have hdimU : Module.finrank (ZMod 2) U ≤ n := by
    have h := Submodule.finrank_le (R := ZMod 2) (M := Fin n → ZMod 2) U
    rwa [hdimV] at h
  omega