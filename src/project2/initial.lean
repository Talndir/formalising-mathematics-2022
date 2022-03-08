/- # Initial objects of F-algebras. -/

import tactic
import category_theory.category.basic
import category_theory.isomorphism
import category_theory.limits.shapes.terminal
import project2.alg

namespace alg

open category_theory category_theory.limits

universes v u
variables {C : Type u} [category.{v} C]

/- We define special notation for the initial object's carrier and algebra, as they are important
   in their own right. -/
noncomputable def μ (F : C ⥤ C) [has_initial (Alg F)] : C := (⊥_ Alg F).A
noncomputable def ins {F : C ⥤ C} [has_initial (Alg F)] : F.obj (μ F) ⟶ μ F := (⊥_ Alg F).a

variables {F : C ⥤ C} [has_initial (Alg F)]

theorem μ_eq_init : ⟪μ F, ins⟫ = (⊥_ Alg F):= (alg_struct (⊥_ Alg F)).symm

noncomputable theorem μ_is_initial : is_initial ⟪μ F, ins⟫ :=
begin
  rw μ_eq_init,
  exact initial_is_initial,
end

/- The catamorphism is the most vital ingredient - the unique map from the initial object, it gets
   its own special notation. -/
noncomputable def cata {A : C} (a : F.obj A ⟶ A) : ⟪μ F, ins⟫ ⟶ ⟨A, a⟩ :=
begin
  rw μ_eq_init,
  exact initial.to ⟪A,a⟫
end

notation `⦃` a `⦄` := cata a

/- Our initial object in `F-Alg` can now be written as `⟪μ F, ins⟫` and the catamorphism of an alg `a` as `⦃a⦄`. -/

theorem uniqueness {A : C} {a : F.obj A ⟶ A} (f : ⟪μ F, ins⟫ ⟶ ⟪A, a⟫) : f = ⦃a⦄ ↔ ins ≫ ↑f = F.map ↑f ≫ a :=
begin
  split; intro h; clear h,
  { exact f.p, },
  { exact is_initial.hom_ext μ_is_initial f ⦃a⦄, }
end

/- The computation law - we can push a computation through `F`. -/
theorem computation {A : C} (a : F.obj A ⟶ A) : ins ≫ ↑⦃a⦄ = F.map ↑⦃a⦄ ≫ a :=
  (uniqueness ⦃a⦄).mp rfl

lemma id_is_id (X : Alg F) : ↑(𝟙 X) = 𝟙 (X.A) := rfl

/- The reflection law. -/
theorem reflection : 𝟙 ⟪μ F, ins⟫ = ⦃ins⦄ :=
begin
  rw uniqueness (𝟙 ⟪μ F, ins⟫),
  rw id_is_id,
  simp,
end

/- The fusion law - two computations can be fused into one. -/
theorem fusion {A B : C} {a : F.obj A ⟶ A} {b : F.obj B ⟶ B} (k : ⟪A,a⟫ ⟶ ⟪B,b⟫) : ⦃a⦄ ≫ k = ⦃b⦄ :=
  is_initial.hom_ext μ_is_initial (⦃a⦄ ≫ k) ⦃b⦄

/- The obvious homomophism from `F (μ F)` to `μ F`. -/
noncomputable def ins_hom : ⟪F.obj (μ F), F.map ins⟫ ⟶ ⟪μ F, ins⟫ :=
{ h := ins,
  p := by tidy }

lemma f_ins_ins_eq_id : ↑⦃F.map ins⦄ ≫ ins = 𝟙 (μ F) :=
begin
  rw ← id_is_id ⟪μ F, ins⟫,
  rw reflection,
  change ↑⦃F.map ins⦄ ≫ ins_hom.h = ↑⦃ins⦄,
  rw [forget_map, forget_map, ← forget_hom, fusion ins_hom],
end

/- Lambek's lemma: the initial object is a fixed point. -/
lemma lambek_lemma : is_iso (ins : F.obj (μ F) ⟶ μ F) :=
{ out := 
  begin
    use ⦃F.map ins⦄,
    split,
    { rw computation,
      rw ← F.map_comp',
      rw f_ins_ins_eq_id,
      rw F.map_id',
    },
    { exact f_ins_ins_eq_id }
  end
}

end alg
 