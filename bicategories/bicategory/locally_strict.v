Require Import HoTT.
Require Import HoTT.Categories.Category Functor NaturalTransformation.
Require Import GR.bicategories.general_category.
Require Import GR.bicategories.bicategory.bicategory.
Require Import GR.bicategories.bicategory.strict.

Class LocallyStrict (C : BiCategory) :=
  set_mor : forall (X Y : C), IsStrictCategory (C⟦X,Y⟧).

Global Instance is_hprop_prestrict
       `{Funext}
       (C : BiCategory)
  : IsHProp (LocallyStrict C).
Proof.
  unfold LocallyStrict.
  apply _.
Qed.

Global Instance is_hset_mor_prestrict
       (C : BiCategory)
       `{LocallyStrict C}
       (X Y : C)
  : IsHSet (C⟦X,Y⟧)
  := set_mor X Y.

Global Instance is_hprop_is_strict
       `{Funext}
       (C : BiCategory)
       `{LocallyStrict C}
  : IsHProp (IsStrict C).
Proof.
  apply hprop_allpath.
  intros S₁ S₂.
  destruct S₁ as [S₁l S₁r S₁a S₁t S₁p S₁il S₁ir S₁ia].
  destruct S₂ as [S₂l S₂r S₂a S₂t S₂p S₂il S₂ir S₂ia].
  assert (S₁l = S₂l) as ->.
  {
    apply path_ishprop.
  }
  assert (S₁r = S₂r) as ->.
  {
    apply path_ishprop.
  }
  assert (S₁a = S₂a) as ->.
  {
    apply path_ishprop.
  }
  assert (S₁t = S₂t) as ->.
  {
    apply path_ishprop.
  }
  assert (S₁p = S₂p) as ->.
  {
    apply path_ishprop.
  }
  assert (S₁il = S₂il) as ->.
  {
    apply path_ishprop.
  }
  assert (S₁ir = S₂ir) as ->.
  {
    apply path_ishprop.
  }
  assert (S₁ia = S₂ia) as ->.
  {
    apply path_ishprop.
  }
  reflexivity.
Qed.

Class is_2category (C : BiCategory) :=
  {
    cat2_is_prestrict : LocallyStrict C ;
    cat2_is_strict : IsStrict C
  }.

Global Instance is_hprop_is_2category
       `{Funext}
       (C : BiCategory)
  : IsHProp (is_2category C).
Proof.
  apply hprop_allpath.
  intros [PSC₁ SC₁] [PSC₂ SC₂].
  assert (PSC₁ = PSC₂) as ->.
  { apply path_ishprop. }
  assert (SC₁ = SC₂) as ->.
  { apply path_ishprop. }
  reflexivity.
Qed.

Definition idtoiso_prod
           {C D : PreCategory}
           {X₁ X₂ : C}
           {Y₁ Y₂ : D}
           (p : X₁ = X₂)
           (q : Y₁ = Y₂)
  : Type.
Proof.
  refine (@morphism_isomorphic (C * D) (X₁,Y₁) (X₂,Y₂) (idtoiso (C * D) (path_prod' p q)) = _).
  refine (@morphism_isomorphic C X₁ X₂ (idtoiso C p),@morphism_isomorphic D Y₁ Y₂ (idtoiso D q)).
Defined.

Definition idtoiso_prod_t
           {C D : PreCategory}
           {X₁ X₂ : C}
           {Y₁ Y₂ : D}
           (p : X₁ = X₂)
           (q : Y₁ = Y₂)
  : idtoiso_prod p q.
Proof.
  unfold idtoiso_prod.
  induction p, q ; cbn.
  reflexivity.
Defined.

Definition idtoiso_1
           {C : PreCategory}
           (X : C)
  : @morphism_isomorphic _ _ _ (idtoiso C (idpath : X = X)) = 1%morphism.
Proof.
  reflexivity.
Defined.

Definition eq_transformation
           {C D : PreCategory}
           {F G : Functor C D}
           (p : F = G)
  : NaturalTransformation F G.
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros X ; cbn.
    exact (idtoiso _ (ap10 (ap object_of p) X)).
  - intros X Y f.
    induction p ; cbn.
    rewrite !left_identity, !right_identity.
    reflexivity.
Defined.

Section Build2Category.
  Variable (Obj : Type)
           (Hom : Obj -> Obj -> StrictCategory)
           (id₁ : forall (X : Obj), Hom X X)
           (hcomp :
              forall {X Y Z : Obj},
                Functor (Hom Y Z * Hom X Y) (Hom X Z))
           (left_unitor :
              forall (X Y : Obj),
                (@hcomp X Y Y o (const_functor (id₁ Y) * 1)  = 1)%functor)
           (right_unitor :
              forall (X Y : Obj),
                (@hcomp X X Y o (1 * const_functor (id₁ X))  = 1)%functor)
           (associator :
              forall (W X Y Z : Obj),
                (@hcomp W Y Z o (Functor.identity (Hom Y Z),@hcomp W X Y)
                 =
                 (@hcomp W X Z)
                   o (@hcomp X Y Z,Functor.identity (Hom W X))
                   o ProductLaws.Associativity.functor _ _ _)%functor)
           (hcomp_id₂ :
              forall {X Y Z : Obj}
                     (f : Hom X Y) (g : Hom Y Z),
                morphism_of hcomp 1%morphism
                =
                (1 : morphism (Hom X Z) (hcomp (g,f)) (hcomp (g,f)))%morphism)
           (interchange :
              forall {X Y Z : Obj}
                     {f₁ g₁ h₁ : Hom Y Z}
                     {f₂ g₂ h₂ : Hom X Y}
                     (α₁ : morphism _ g₁ h₁) (β₁ : morphism _ f₁ g₁)
                     (α₂ : morphism _ g₂ h₂) (β₂ : morphism _ f₂ g₂),
                (@morphism_of _ _ hcomp (f₁,f₂) (h₁,h₂) (α₁ o β₁,α₂ o β₂)
                 =
                 (@morphism_of _ _ hcomp (g₁,g₂) (h₁,h₂) (α₁,α₂))
                   o (@morphism_of _ _ hcomp (f₁,f₂) (g₁,g₂) (β₁,β₂)))%morphism).
  
  Definition Build_2Category_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact Obj.
    - exact Hom.
    - exact id₁.
    - intros X Y Z ; cbn.
      exact (object_of (hcomp X Y Z)).
    - intros X Y Z f g α.
      exact (morphism_of (hcomp X Y Z) α).
    - intros X Y f ; cbn.
      exact (idtoiso _ (ap10 (ap object_of (left_unitor X Y)) f)).
    - intros X Y f ; cbn.
      exact (idtoiso _ (ap10 (ap object_of (left_unitor X Y)^) f)).
    - intros X Y f ; cbn.
      exact (idtoiso _ (ap10 (ap object_of (right_unitor X Y)) f)).
    - intros X Y f ; cbn.
      exact (idtoiso _ (ap10 (ap object_of (right_unitor X Y)^) f)).
    - intros W X Y Z h g f ; cbn in *.
      exact (idtoiso _ (ap10 (ap object_of (associator W X Y Z)^) (h,(g,f)))).
    - intros W X Y Z h g f ; cbn in *.
      exact (idtoiso _ (ap10 (ap object_of (associator W X Y Z)) (h,(g,f)))).
  Defined.

  Definition Build_2Category_is_bicategory : is_bicategory Build_2Category_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z [f g] ; cbn in *.
      apply hcomp_id₂.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [α₁ α₂] [β₁ β₂] ; cbn in *.
      apply interchange.
    - intros ; cbn.
      exact (commutes (eq_transformation (left_unitor X Y)) f g η).
    - intros ; cbn.
      exact (commutes (eq_transformation (left_unitor X Y)^) f g η).
    - intros ; cbn.
      exact (commutes (eq_transformation (right_unitor X Y)) f g η).
    - intros ; cbn.
      exact (commutes (eq_transformation (right_unitor X Y)^) f g η).
    - intros X Y f ; cbn.
      rewrite idtoiso_comp.
      rewrite <- (ap10_pp (ap object_of (left_unitor X Y)^)
                          (ap object_of (left_unitor X Y))).
      rewrite <- ap_pp, concat_Vp.
      reflexivity.
    - intros X Y f ; cbn.
      rewrite idtoiso_comp.
      rewrite <- (ap10_pp (ap object_of (left_unitor X Y))
                          (ap object_of (left_unitor X Y)^)).
      rewrite <- ap_pp, concat_pV.
      reflexivity.
    - intros X Y f ; cbn.
      rewrite idtoiso_comp.
      rewrite <- (ap10_pp (ap object_of (right_unitor X Y)^)
                          (ap object_of (right_unitor X Y))).
      rewrite <- ap_pp, concat_Vp.
      reflexivity.
    - intros X Y f ; cbn.
      rewrite idtoiso_comp.
      rewrite <- (ap10_pp (ap object_of (right_unitor X Y))
                          (ap object_of (right_unitor X Y)^)).
      rewrite <- ap_pp, concat_pV.
      reflexivity.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; cbn.
      exact (commutes (eq_transformation (associator W X Y Z)^)
                      (h₁,(g₁,f₁))
                      (h₂,(g₂,f₂))
                      (ηh,(ηg,ηf))).
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; cbn.
      exact (commutes (eq_transformation (associator W X Y Z))
                      (h₁,(g₁,f₁))
                      (h₂,(g₂,f₂))
                      (ηh,(ηg,ηf))).
    - intros W X Y Z f g h ; cbn.
      rewrite idtoiso_comp.
      rewrite <- (ap10_pp (ap object_of (associator W X Y Z))
                          (ap object_of (associator W X Y Z)^)).
      rewrite <- ap_pp, concat_pV.
      reflexivity.
    - intros W X Y Z f g h ; cbn.
      rewrite idtoiso_comp.
      rewrite <- (ap10_pp (ap object_of (associator W X Y Z)^)
                          (ap object_of (associator W X Y Z))).
      rewrite <- ap_pp, concat_Vp.
      reflexivity.
    - intros ; cbn.
      rewrite <- !idtoiso_1.
      rewrite <- !idtoiso_prod_t.
      rewrite !idtoiso_functor.
      rewrite idtoiso_comp.
      repeat f_ap.
      apply path_ishprop.
    - intros ; cbn.
      rewrite <- !idtoiso_1.
      rewrite <- !idtoiso_prod_t.
      rewrite !idtoiso_functor.
      rewrite !idtoiso_comp.
      repeat f_ap.
      apply path_ishprop.
  Qed.

  Definition Build_2Category : BiCategory
    := Build_BiCategory Build_2Category_d Build_2Category_is_bicategory.

  Global Instance Build_2Category_is_2category
    : is_2category Build_2Category.
  Proof.
    split.
    - intros X Y.
      apply (Hom X Y).
    - make_strict.
      + intros X Y f.
        exact (ap10 (ap object_of (left_unitor X Y)) f).
      + intros X Y f.
        exact (ap10 (ap object_of (right_unitor X Y)) f).
      + intros W X Y Z h g f.
        exact (ap10 (ap object_of (associator W X Y Z)^) (h,(g,f))).
      + intros ; apply path_ishprop.
      + intros ; apply path_ishprop.
      + reflexivity.
      + reflexivity.
      + reflexivity.
  Defined.
End Build2Category.