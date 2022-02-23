/- # Algebras over endofunctors. -/

import tactic
import category_theory.category.basic
import category_theory.functor

namespace project2

open category_theory

universes v u
variables {C : Type u} [category.{v} C]

/-- Let `F : C ⟶ C` be an endofunctor. `F-Alg(C)` is a category with objects `(A, a)`
    such that `A : C` and `a : F A ⟶ A`. `A` is called the carrier and `a` the algebra. -/
structure Algebra (F : C ⥤ C) : Type (max u v) :=
(A : C)
(a : F.obj A ⟶ A)

variable {F : C ⥤ C}

/-- Homomorphisms between `X Y : F-Alg(C)` are simply homomorphisms `X ⟶ Y`
    that respect the functoriality of F. -/
@[ext] structure hom (X Y : Algebra F) : Type v :=
(h : X.A ⟶ Y.A)
(p : X.a ≫ h = F.map h ≫ Y.a)

/-- The identity of an object `X : F-Alg` is just the identity on `X.A`. -/
def id (X : Algebra F) : hom X X :=
{ h := 𝟙 X.A,
  p := begin simp end }

/-- Composition is the composition of the underlying homomorphisms. -/
def comp {X Y Z : Algebra F} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ h := f.h ≫ g.h,
  p := begin
    rw [F.map_comp', ← category.assoc],
    rw [f.p, category.assoc],
    rw [g.p, category.assoc],
  end
}

/- We do the `category_struct` first to get access to the `⟶` and `𝟙` syntax. -/
instance algebra.category_struct (F : C ⥤ C) : category_struct (Algebra F) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z, comp, }

/- These axioms of a category are marked `obviously`, but in this case they are not
   trivial enough to be solved by `tidy` (which is what `obviously` actually calls)
   so we need to do them by hand. -/

/- To put it another way: `.h` is a homomorphism with respect to `≫`. -/
@[simp] lemma comp_h_eq_h_comp {X Y Z : Algebra F} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).h = f.h ≫ g.h := rfl

/-- `𝟙` is a left identity. -/
theorem id_comp' {X Y : Algebra F} (f : X ⟶ Y) : 𝟙 X ≫ f = f :=
begin
  ext,
  rw comp_h_eq_h_comp,
  change 𝟙 X.A ≫ f.h = f.h,
  simp,
end

/-- `𝟙` is a right identity. -/
theorem comp_id' {X Y : Algebra F} (f : X ⟶ Y) : f ≫ 𝟙 Y = f :=
begin
  ext,
  rw comp_h_eq_h_comp,
  change f.h ≫ 𝟙 Y.A = f.h,
  simp,
end

/-- `≫` is associative. -/
theorem assoc' {W X Y Z : Algebra F} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
  (f ≫ g) ≫ h = f ≫ g ≫ h :=
begin
  ext,
  repeat { rw comp_h_eq_h_comp },
  simp,
end

instance algebra.category (F : C ⥤ C) : category (Algebra F) :=
{ id_comp' := λ X Y, id_comp',
  comp_id' := λ X Y, comp_id',
  assoc' := λ W X Y Z, assoc', }

end project2
