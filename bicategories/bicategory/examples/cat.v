Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory bicategory.univalent.
From GR.bicategories.bicategory.examples Require Import
     precat full_sub.

Definition Cat `{Univalence} : BiCategory
  := full_sub PreCat (fun C => BuildhProp (IsCategory C)).