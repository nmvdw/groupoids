Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.adjoint
     bicategory.univalent
     bicategory.locally_strict
     bicategory.strict.

Section ArrowSubcategory.
  Variable (C : BiCategory)
           (P : forall (X Y : C), C⟦X,Y⟧ -> hProp)
           (Pid : forall (X : C), P X X (id₁ X))
           (Pcomp : forall (X Y Z : C) (f : C⟦X,Y⟧) (g : C⟦Y,Z⟧),
               P X Y f -> P Y Z g -> P X Z (g · f)).

  Definition arrow_subcat_morphisms (X Y : C) : PreCategory.
  Proof.
    simple refine (@Build_PreCategory
                     {f : C⟦X,Y⟧ & P X Y f}
                     (fun f g => morphism (C⟦X,Y⟧) f.1 g.1)
                     _ _ _ _ _ _).
    - intros [f Hf] ; simpl in *.
      exact (id₂ f).
    - intros [f Hf] [g Hg] [h Hh] α β ; simpl in *.
      exact (α ∘ β).
    - intros [f₁ Hf₁] [f₂ Hf₂] [f₃ Hf₃] [f₄ Hf₄] α₁ α₂ α₃ ; simpl in *.
      apply vcomp_assoc.
    - intros [f Hf] [g Hg] α ; simpl in *.
      apply vcomp_left_identity.
    - intros [f Hf] [g Hg] α ; simpl in *.
      apply vcomp_right_identity.
  Defined.

  Definition arrow_subcat_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact C.
    - intros X Y.
      exact (arrow_subcat_morphisms X Y).
    - intros X ; simpl in *.
      exact (id₁ X;Pid X).
    - intros X Y Z [[f Hf] [g Hg]] ; simpl in *.
      exact (f · g;Pcomp X Y Z g f Hg Hf).
    - intros X Y Z [[f₁ Hf₁] [g₁ Hg₁]] [[f₂ Hf₂] [g₂ Hg₂]] [α β] ; simpl in *.
      exact (α * β).
    - intros X Y [f Hf] ; simpl in *.
      exact (left_unit f).
    - intros X Y [f Hf] ; simpl in *.
      exact (left_unit_inv f).
    - intros X Y [f Hf] ; simpl in *.
      exact (right_unit f).
    - intros X Y [f Hf] ; simpl in *.
      exact (right_unit_inv f).
    - intros W X Y Z [h Hh] [g Hg] [f Hf] ; simpl in *.
      exact (assoc h g f).
    - intros W X Y Z [h Hh] [g Hg] [f Hf] ; simpl in *.
      exact (assoc_inv h g f).
  Defined.

  Definition arrow_subcat_is_bicategory : is_bicategory arrow_subcat_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z [[f Hf] [g Hg]] ; simpl in *.
      exact (hcomp_id₂ f g).
    - intros X Y Z
             [[f₁ Hf₁] [g₁ Hg₁]] [[f₂ Hf₂] [g₂ Hg₂]] [[f₃ Hf₃] [g₃ Hg₃]]
             [α₁ α₂] [β₁ β₂]
      ; simpl in *.
      apply interchange.
    - intros X Y f g α ; simpl in *.
      apply left_unit_natural.
    - intros X Y f g α ; simpl in *.
      apply left_unit_inv_natural.
    - intros X Y f g α ; simpl in *.
      apply right_unit_natural.
    - intros X Y f g α ; simpl in *.
      apply right_unit_inv_natural.
    - intros X Y f ; simpl in *.
      apply left_unit_left.
    - intros X Y f ; simpl in *.
      apply left_unit_right.
    - intros X Y f ; simpl in *.
      apply right_unit_left.
    - intros X Y f ; simpl in *.
      apply right_unit_right.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      apply assoc_natural.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ηh ηg ηf ; simpl in *.
      apply assoc_inv_natural.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_left.
    - intros W X Y Z f g h ; simpl in *.
      apply assoc_right.
    - intros X Y Z g f ; simpl in *.
      apply triangle_r.
    - intros V W X Y Z k h g f ; simpl in *.
      apply pentagon.
  Qed.

  Definition arrow_subcat : BiCategory
    := Build_BiCategory arrow_subcat_d arrow_subcat_is_bicategory.

  Global Instance locally_univalent_arrow_subcat
         `{Univalence}
         {HC : LocallyUnivalent C}
    : LocallyUnivalent arrow_subcat.
  Proof.
    intros X Y ; cbn.
    apply _.
  Defined.

  Global Instance locally_strict_arrow_subcat
         {HC : LocallyStrict C}
    : LocallyStrict arrow_subcat.
  Proof.
    intros X Y.
    apply _.
  Qed.

  Global Instance is_isomorphism_arrow_subcat
         {X Y : C}
         (f g : C⟦X,Y⟧)
         (Hf : P _ _ f)
         (Hg : P _ _ g)
         (α : f ==> g)
         `{IsIsomorphism _ _ _ α}
    : @IsIsomorphism (arrow_subcat_morphisms X Y) (f;Hf) (g;Hg) α.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _) ; apply H.
  Defined.

  Definition idtoiso_arrow_subcat
             {X Y : C}
             (f g : C⟦X,Y⟧)
             (Hf : P _ _ f)
             (Hg : P _ _ g)
             (p : f = g)
    : idtoiso (arrow_subcat_morphisms X Y) (path_sigma_hprop (f;Hf) (g;Hg) p)
      =
      @Build_Isomorphic (arrow_subcat_morphisms X Y) (f;Hf) (g;Hg) (idtoiso _ p) _.
  Proof.
    apply path_isomorphic.
    induction p ; cbn.
    assert (Hf = Hg) as ->.
    { apply path_ishprop. }
    rewrite path_sigma_hprop_1.
    reflexivity.
  Qed.

  Definition whisker_l_arrow_subcat
             {X Y  Z: C}
             (f : arrow_subcat⟦X,Y⟧)
             (g₁ g₂ : arrow_subcat⟦Y,Z⟧)
             (p : g₁.1 = g₂.1)
    : ap (fun (g : arrow_subcat⟦Y,Z⟧) => g · f) (path_sigma_hprop g₁ g₂ p)
      =
      path_sigma_hprop (g₁ · f) (g₂ · f) (ap (fun g => g · f.1) p).
  Proof.
    destruct g₁ as [g₁ Hg₁], g₂ as [g₂ Hg₂] ; simpl in *.
    induction p ; simpl.
    assert (Hg₁ = Hg₂) as ->.
    { apply path_ishprop. }
    rewrite !path_sigma_hprop_1.
    reflexivity.
  Defined.

  Definition whisker_r_arrow_subcat
             {X Y  Z: C}
             (f₁ f₂ : arrow_subcat⟦X,Y⟧)
             (g : arrow_subcat⟦Y,Z⟧)
             (p : f₁.1 = f₂.1)
    : ap (fun (f : arrow_subcat⟦X,Y⟧) => g · f) (path_sigma_hprop f₁ f₂ p)
      =
      path_sigma_hprop (g · f₁) (g · f₂) (ap (fun f => g.1 · f) p).
  Proof.
    destruct f₁ as [f₁ Hf₁], f₂ as [f₂ Hf₂] ; simpl in *.
    induction p ; simpl.
    assert (Hf₁ = Hf₂) as ->.
    { apply path_ishprop. }
    rewrite !path_sigma_hprop_1.
    reflexivity.
  Defined.

  Definition is_strict_arrow_subcat
             (HC : IsStrict C)
    : IsStrict arrow_subcat.
  Proof.
    make_strict.
    - intros X Y f ; simpl in *.
      apply path_sigma_hprop.
      exact (strict_left_unit HC f.1).
    - intros X Y f ; simpl in *.
      apply path_sigma_hprop.
      exact (strict_right_unit HC f.1).
    - intros W X Y Z h g f ; simpl in *.
      apply path_sigma_hprop.
      exact (strict_assoc HC h.1 g.1 f.1).
    - intros X Y Z g f ; simpl.
      rewrite whisker_l_arrow_subcat, whisker_r_arrow_subcat.
      rewrite <- path_sigma_hprop_pp.
      f_ap.
      apply HC.
    - intros V W X Y Z k h g f ; simpl.
      rewrite whisker_l_arrow_subcat, whisker_r_arrow_subcat.
      rewrite <- !path_sigma_hprop_pp.
      f_ap.
      apply HC.
    - intros X Y f ; simpl.
      rewrite idtoiso_arrow_subcat ; simpl.
      apply HC.
    - intros X Y f ; simpl.
      rewrite idtoiso_arrow_subcat ; simpl.
      apply HC.
    - intros W X Y Z h g f ; simpl.
      rewrite idtoiso_arrow_subcat ; simpl.
      apply HC.
  Defined.

  Global Instance is_2category_arrow_subcategory
         `{H : is_2category C}
    : is_2category arrow_subcat.
  Proof.
    split.
    - destruct H.
      apply _.
    - apply is_strict_arrow_subcat.
      apply H.
  Defined.

  Global Instance arrow_subcategory_isomorphism
         {X Y : C}
         {f g : C⟦X,Y⟧}
         (Hf : P _ _ f)
         (Hg : P _ _ g)
         (α : f ==> g)
         `{@IsIsomorphism (C⟦X,Y⟧) f g α}
    : @IsIsomorphism (arrow_subcat⟦X,Y⟧) (f;Hf) (g;Hg) α
    := _.
End ArrowSubcategory.