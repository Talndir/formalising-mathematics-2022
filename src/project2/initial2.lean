/- # Initial objects of F-algebras - version 2. -/

import tactic
import category_theory.category.basic
import category_theory.functor
import category_theory.functor_category
import category_theory.natural_transformation
import category_theory.limits.shapes.terminal
import project2.alg
import project2.initial

namespace alg

open category_theory category_theory.limits

universes v u

/- Let `C` be a category. Then `IAlg(C)` is the category of `F-Alg(C)` for all `F : C ⥤ C`,
   such that `F-Alg(C)` has an initial object. -/
@[ext] structure IAlg (C : Type u) [category.{v} C]: Type (max u v) :=
(F : C ⥤ C)
[p : has_initial (Alg F)]

variables {C : Type u} [category.{v} C]

instance ialg.has_initial (F : IAlg C) : has_initial (Alg F.F) := F.p

/- A functor between `F-Alg` and `G-Alg` is a natural transformation from `F` to `G`.
   The properties follow directly from what we know about natural transformations. -/
instance ialg.category : category (IAlg C) :=
{ hom := λ F G, F.F ⟶ G.F,
  id := λ F, 𝟙 F.F,
  comp := λ F G H, λ f g, f ≫ g,
  id_comp' := λ F G, by tidy,
  comp_id' := λ F G, by tidy,
  assoc' := λ F G H I, λ f g h, by tidy }

/- We are going to define `Mu : (C ⥤ C) ⥤ C`, where `Mu F` is only defined if `F-Alg` has an initial object.
   This is like the `μ` from before, but as a proper functor rather than just a map. -/

/- The action on objects: `Mu f = μ F`. -/
noncomputable def obj (F : IAlg C) : C := μ F.F

/- The action on arrows (natural transformations): `Mu α = ⦃ins . α (μ G)⦄`. -/
noncomputable def map {F G : IAlg C} (α : F ⟶ G) : (μ F.F) ⟶ (μ G.F) := ⦃α.app (μ G.F) ≫ ins⦄

theorem map_def {F G : IAlg C} (α : F ⟶ G) : map α = ⦃α.app (μ G.F) ≫ ins⦄ := rfl

/- Base functor fusion. -/
theorem base_fusion {F G : IAlg C} {A : C} (a : G.F.obj A ⟶ A) (α : F ⟶ G) :
  (map α) ≫ ⦃a⦄.h = ↑⦃α.app A ≫ a⦄ :=
begin
  rw map,
  sorry
end

/- Identity is preserved. -/
theorem map_id' (F : IAlg C) : map (𝟙 F) = 𝟙 (obj F) :=
begin
  have p : 𝟙 F = nat_trans.id F.F := rfl,
  rw [map, p, nat_trans.id_app', category.id_comp, ← reflection],
  refl,
end

/- Composition is preserved. -/
theorem map_comp' {F G H : IAlg C} (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ≫ map β :=
begin
  rw map,
  have h : (α ≫ β).app (μ H.F) = α.app (μ H.F) ≫ β.app (μ H.F) := nat_trans.comp_app α β (μ H.F),
  rw [h, category.assoc, ← base_fusion],
  have h' : ⦃β.app (μ H.F) ≫ ins⦄.h = ↑⦃β.app (μ H.F) ≫ ins⦄ := rfl,
  rw [h', ← map_def β],
end

/- `Mu` is a functor. -/
noncomputable def Mu : IAlg C ⥤ C :=
{ obj := obj,
  map := λ F G, map,
  map_id' := map_id',
  map_comp' := λ X Y Z, map_comp' }

end alg
