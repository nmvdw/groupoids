Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.prestrict
     bicategory.strict
     adjoint
     adjoint_unique.
From GR.bicategories.bicategory.examples Require Import
     precat full_sub.

Definition StrictCat `{Funext} : BiCategory
  := full_sub PreCat (fun C => BuildhProp (IsStrictCategory C)).

Global Instance prestrict_strict_cat `{Funext}
  : prestrict StrictCat.
Proof.
  intros [C SC] [Y SY].
  apply _.
Qed.

Definition IsStrict_StrictCat `{Funext} : IsStrict StrictCat
  := full_sub_strict _ _ StrictPreCat.

Global Instance is_2category_StrictCat
       `{Funext}
  : is_2category StrictCat.
Proof.
  split.
  - apply _.
  - apply IsStrict_StrictCat.
Defined.