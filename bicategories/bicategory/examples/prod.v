Require Import HoTT.
From HoTT.Categories Require Import
     Category Category.Prod NaturalTransformation FunctorCategory.
Require Import bicategory.

Local Notation "x ₁" := (Datatypes.fst x) (at level 80).
Local Notation "x ₂" := (Datatypes.snd x) (at level 80).

Section ProductBicategory.
  Context `{Univalence}.
  Variable (C D : BiCategory).
  
  Definition prod_obj : Type
    := Obj C * Obj D.
  
  Definition prod_hom : prod_obj -> prod_obj -> PreCategory
    := fun x y => Category.Prod.prod (Hom C (x ₁) (y ₁))
                                     (Hom D (x ₂) (y ₂)).

  Definition prod_id_m (x : prod_obj) : prod_hom x x
    := (id_m (x ₁), id_m (x ₂)).

  Definition prod_c_m (x y z : prod_obj)
    : Functor (prod_hom y z * prod_hom x y) (prod_hom x z).
  Proof.
    pose (@c_m _ C (x ₁) (y ₁) (z ₁)) as F₁.
    pose (@c_m _ D (x ₂) (y ₂) (z ₂)) as F₂.
    simple refine (Build_Functor _ _ _ _ _ _).
    - intros [[f₁ f₂] [g₁ g₂]] ; cbn in *.
      exact (F₁ (f₁,g₁), F₂ (f₂,g₂)).
    - intros [a₁ a₂] [b₁ b₂] [[f₁ f₂] [g₁ g₂]] ; cbn in *.
      refine (F₁ _1 _, F₂ _1 _)%morphism.
      + exact (f₁,g₁).
      + exact (f₂,g₂).
    - intros [a₁ a₂] [b₁ b₂] [c₁ c₂] [[f₁ f₂] [g₁ g₂]] [[h₁ h₂] [k₁ k₂]] ; cbn in *.
      apply path_prod'.
      + exact (composition_of F₁ (a₁ ₁, a₂ ₁) (b₁ ₁, b₂ ₁) (c₁ ₁, c₂ ₁) (f₁,g₁) (h₁,k₁)).
      + exact (composition_of F₂ (a₁ ₂, a₂ ₂) (b₁ ₂, b₂ ₂) (c₁ ₂, c₂ ₂) (f₂,g₂) (h₂,k₂)).
    - intros [a₁ a₂] ; cbn.
      apply path_prod' ; apply identity_of.
  Defined.

  Definition prUnitor_l (x y : prod_obj)
    : NaturalTransformation
        (prod_c_m x y y o (@const_functor _ (prod_hom y y) (prod_id_m y) * 1))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - cbn ; intros.
      split ; apply (Core.components_of (un_l _ _)).
    - cbn ; intros ? ? p.
      apply path_prod' ; apply un_l.
  Defined.

  Definition prUnitor_l_inv (x y : prod_obj)
    : NaturalTransformation
        1
        (prod_c_m x y y o (@const_functor _ (prod_hom y y) (prod_id_m y) * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - cbn ; intros.
      split ; refine ((un_l _ _ _)^-1)%morphism.
    - cbn ; intros.
      apply path_prod'.
      + exact (commutes (inverse (@un_l _ _ _ _)) _ _ (m ₁)).
      + exact (commutes (inverse (@un_l _ _ _ _)) _ _ (m ₂)).
  Defined.

  Global Instance prUnitor_l_iso (x y : prod_obj)
    : @IsIsomorphism (prod_hom x y -> prod_hom x y) _ _ (prUnitor_l x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply prUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros [p₁ p₂] ; cbn in *.
      apply path_prod' ; cbn
      ; refine (_ @ left_inverse) ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [p₁ p₂] ; cbn in *.
      apply path_prod' ; cbn
      ; refine (_ @ right_inverse) ; reflexivity.
  Defined.

  Definition prUnitor_r (x y : prod_obj)
    : NaturalTransformation
        (prod_c_m x x y o (1 * @const_functor (prod_hom x y) (prod_hom x x) (prod_id_m x)))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - cbn ; intros.
      split ; apply (Core.components_of (un_r _ _)).
    - cbn ; intros ? ? p.
      apply path_prod' ; apply un_r.
  Defined.

  Definition prUnitor_r_inv (x y : prod_obj)
    : NaturalTransformation
        1
        (prod_c_m x x y o (1 * @const_functor (prod_hom x y) (prod_hom x x) (prod_id_m x))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - cbn ; intros.
      split ; refine ((un_r _ _ _)^-1)%morphism.
    - cbn ; intros.
      apply path_prod'.
      + exact (commutes (inverse (@un_r _ _ _ _)) _ _ (m ₁)).
      + exact (commutes (inverse (@un_r _ _ _ _)) _ _ (m ₂)).
  Defined.

  Global Instance prUnitor_r_iso (x y : prod_obj)
    : @IsIsomorphism (prod_hom x y -> prod_hom x y) _ _ (prUnitor_r x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply prUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros [p₁ p₂] ; cbn in *.
      apply path_prod' ; cbn
      ; refine (_ @ left_inverse) ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [p₁ p₂] ; cbn in *.
      apply path_prod' ; cbn
      ; refine (_ @ (@right_inverse _ _ _ (un_r _ _ _) _)) ; reflexivity.
  Defined.
  
  Definition prAssociator (w x y z : prod_obj)
    : NaturalTransformation
        (prod_c_m w x z o (prod_c_m x y z, 1))
        (prod_c_m w y z o (1, prod_c_m w x y)
                  o assoc_prod (prod_hom y z) (prod_hom x y) (prod_hom w x)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros [[f₁ f₂] f₃] ; cbn in *.
      split.
      + exact (assoc (f₁ ₁, f₂ ₁, f₃ ₁)).
      + exact (assoc (f₁ ₂, f₂ ₂, f₃ ₂)).
    - intros [[a₁ a₂] a₃] [[b₁ b₂] b₃] [[f₁ f₂] f₃] ; cbn in *.
      apply path_prod'.
      + exact (commutes (@assoc _ C (w ₁) (x ₁) (y ₁) (z ₁))
                       (a₁ ₁,a₂ ₁,a₃ ₁)
                       (b₁ ₁,b₂ ₁,b₃ ₁)
                       (f₁ ₁,f₂ ₁,f₃ ₁)).
      + exact (commutes (@assoc _ D (w ₂) (x ₂) (y ₂) (z ₂))
                        (a₁ ₂,a₂ ₂,a₃ ₂)
                        (b₁ ₂,b₂ ₂,b₃ ₂)
                        (f₁ ₂,f₂ ₂,f₃ ₂)).
  Defined.

  Definition prAssociator_inv (w x y z : prod_obj)
    : NaturalTransformation
        (prod_c_m w y z o (1, prod_c_m w x y)
                  o assoc_prod (prod_hom y z) (prod_hom x y) (prod_hom w x))
        (prod_c_m w x z o (prod_c_m x y z, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - intros [[f₁ f₂] f₃] ; cbn in *.
      split.
      + exact ((assoc (f₁ ₁, f₂ ₁, f₃ ₁))^-1)%morphism.
      + exact ((assoc (f₁ ₂, f₂ ₂, f₃ ₂))^-1)%morphism.
    - intros [[a₁ a₂] a₃] [[b₁ b₂] b₃] [[f₁ f₂] f₃] ; cbn in *.
      apply path_prod'.
      + exact (commutes (inverse
                           (@assoc _
                                   C
                                   (w ₁) (x ₁) (y ₁) (z ₁)
                           )
                        )
                        (a₁ ₁,a₂ ₁,a₃ ₁)
                        (b₁ ₁,b₂ ₁,b₃ ₁)
                        (f₁ ₁,f₂ ₁,f₃ ₁)).
      + exact (commutes (inverse
                           (@assoc _
                                   D
                                   (w ₂) (x ₂) (y ₂) (z ₂)
                           )
                        )
                        (a₁ ₂,a₂ ₂,a₃ ₂)
                        (b₁ ₂,b₂ ₂,b₃ ₂)
                        (f₁ ₂,f₂ ₂,f₃ ₂)).
  Defined.

  Global Instance prAssociator_iso (w x y z : prod_obj)
    : @IsIsomorphism ((prod_hom y z * prod_hom x y) * prod_hom w x
                      -> prod_hom w z)
                     _ _ (prAssociator w x y z).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply prAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [p₁ p₂] ; cbn in *.
      apply path_prod' ; cbn.
      + exact (@left_inverse _ _ _ (assoc ((p₁ ₁) ₁, (p₁ ₂) ₁, p₂ ₁)) _).
      + exact (@left_inverse _ _ _ (assoc ((p₁ ₁) ₂, (p₁ ₂) ₂, p₂ ₂)) _).
    - cbn.
      apply path_natural_transformation.
      intros [p₁ p₂] ; cbn in *.
      apply path_prod' ; cbn.
      + exact (@right_inverse _ _ _ (assoc ((p₁ ₁) ₁, (p₁ ₂) ₁, p₂ ₁)) _).
      + exact (@right_inverse _ _ _ (assoc ((p₁ ₁) ₂, (p₁ ₂) ₂, p₂ ₂)) _).
  Defined.

  Definition prod
    : BiCategory.
  Proof.
    simple refine {|Obj := prod_obj ;
                    Hom := prod_hom ;
                    id_m := prod_id_m ;
                    c_m := prod_c_m ;
                    un_l := prUnitor_l ;
                    un_l_iso := prUnitor_l_iso ;
                    un_r := prUnitor_r ;
                    un_r_iso := prUnitor_r_iso ;
                    assoc := prAssociator ;
                    assoc_iso := prAssociator_iso ;
                    triangle_r := _ ;
                    pentagon := _|}.
    - intros.
      apply path_prod' ; apply triangle_r.
    - intros.
      apply path_prod' ; apply pentagon.
  Defined.
End ProductBicategory.
