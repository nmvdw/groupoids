Require Import HoTT.
From HoTT.Categories Require Export
  Category Functor NaturalTransformation FunctorCategory.

Definition const_functor
           {C D : PreCategory}
           (X : D)
  : Functor C D
  := Build_Functor C
                   D
                   (fun _ => X)
                   (fun _ _ _ => Category.identity X)
                   (fun _ _ _ _ _ => (left_identity _ _ _ _)^)
                   (fun _ => idpath).

Definition assoc_prod (C D E : PreCategory)
  : Functor ((C * D) * E) (C * (D * E))
  := fst o fst * (snd o fst * snd).

Definition pair
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F₁ F₂ : Functor C₁ C₂}
           {G₁ G₂ : Functor D₁ D₂}
           (af : NaturalTransformation F₁ F₂)
           (ag : NaturalTransformation G₁ G₂)
  : NaturalTransformation (F₁,G₁) (F₂,G₂).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact (fun X => (af (fst X),ag (snd X))).
  - exact (fun X Y f => path_prod' (commutes af _ _ _) (commutes ag _ _ _)).
Defined.