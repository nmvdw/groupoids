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

Definition inverse_compose
           {C : PreCategory}
           {X Y Z : C}
           (g : morphism C Y Z) (f : morphism C X Y)
           `{IsIsomorphism C _ _ f} `{IsIsomorphism C _ _ g}
  : ((g o f)^-1 = f^-1 o g^-1)%morphism
  := idpath.

Definition inverse_id
           {C : PreCategory}
           (X : C)
  : (1^-1 = Core.identity X)%morphism
  := idpath.

Global Instance iso_pair
       {C D : PreCategory}
       {XC YC : C}
       {XD YD : D}
       (f : morphism C XC YC) (g : morphism D XD YD)
       `{IsIsomorphism C _ _ f} `{IsIsomorphism D _ _ g}
  : IsIsomorphism ((f,g) : morphism (Category.Prod.prod C D) (XC,XD) (YC,YD)).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (f^-1,g^-1)%morphism.
  - exact (path_prod' left_inverse left_inverse).
  - exact (path_prod' right_inverse right_inverse).
Defined.

Definition inverse_pair
           {C D : PreCategory}
           {XC YC : C}
           {XD YD : D}
           (f : morphism C XC YC) (g : morphism D XD YD)
           `{IsIsomorphism C _ _ f} `{IsIsomorphism D _ _ g}
  : (((f,g) : morphism (Category.Prod.prod C D) (XC,XD) (YC,YD))^-1)%morphism
    = (f^-1,g^-1)%morphism
  := idpath.

Definition inverse_of
           {C D : PreCategory}
           {X Y : C}
           (F : Functor C D)
           (f : morphism C X Y)
           `{IsIsomorphism C _ _ f}
  : (morphism_of F (f^-1) = (morphism_of F f)^-1)%morphism
  := idpath.

Definition path_inverse
           {C : PreCategory}
           {X Y : C}
           (f g : morphism C X Y)
           `{IsIsomorphism C _ _ f} `{IsIsomorphism C _ _ g}
  : f = g -> (f^-1 = g^-1)%morphism.
Proof.
  intros p ; induction p.
  refine ((right_identity _ _ _ _)^ @ _).
  refine (ap _ (@right_inverse _ _ _ f _)^ @ _).
  refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
  refine (ap (fun z => z o _)%morphism (@left_inverse _ _ _ f _) @ _).
  apply left_identity.
Defined.