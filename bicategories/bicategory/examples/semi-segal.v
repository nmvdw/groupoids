Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.strict
     bicategory.univalent
     bicategory.adjoint
     bicategory.adjoint_unique.

Section SemiSegalType.
  Variable (Ob : Type)
           (Hom : Ob -> Ob -> Type)
           (id : forall (X : Ob), Hom X X)
           (comp : forall (X Y Z : Ob), Hom Y Z -> Hom X Y -> Hom X Z).
  Context `{forall (X Y : Ob), IsTrunc 1 (Hom X Y)}.

  Local Notation "f 'oc' g" := (comp _ _ _ f g) (at level 60).

  Variable (λ : forall {X Y : Ob} (f : Hom X Y),
               id Y oc f = f)
           (ρ : forall {X Y : Ob} (f : Hom X Y),
               f oc id X = f)
           (α : forall {W X Y Z : Ob}
                       (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
               h oc (g oc f) = (h oc g) oc f)
           (trianglator : forall (X Y Z : Ob)
                                 (g : Hom Y Z) (f : Hom X Y),
               ap (fun z => g oc z) (λ f)
               =
               α g (id Y) f
                 @ ap (fun z => z oc f) (ρ g))
           (pentagonator : forall (V W X Y Z : Ob)
                                  (k : Hom Y Z) (h : Hom X Y)
                                  (g : Hom W X) (f : Hom V W),
               α k h (g oc f) @ α (k oc h) g f
               = ap (fun z => k oc z) (α h g f)
                    @ α k (h oc g) f
                    @ ap (fun z => z oc f) (α k h g)).
  
  Definition SemiSegalType_bicat_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact Ob.
    - intros X Y.
      simple refine (@Build_PreCategory (Hom X Y) (fun f g => f = g) _ _ _ _ _ _) ; cbn.
      + exact (@idpath _).
      + intros ? ? ? p q.
        exact (q @ p).
      + intros ; cbn.
        apply concat_p_pp.
      + intros ; cbn.
        apply concat_p1.
      + intros ; cbn.
        apply concat_1p.
    - exact id.
    - intros ? ? ? f ; cbn in *.
      exact ((fst f) oc (snd f)).
    - intros ? ? ? ? ? p ; cbn in *.
      exact (ap (fun z => _ oc z) (snd p) @ ap (fun z => z oc _) (fst p)).
    - exact λ.
    - intros ; cbn in *.
      symmetry.
      apply λ.
    - exact ρ.
    - intros ; cbn in *.
      symmetry.
      apply ρ.
    - intros ; cbn in *.
      symmetry.
      apply α.
    - exact α.
  Defined.

  Definition SemiSegalType_is_bicategory : is_bicategory SemiSegalType_bicat_d.
  Proof.
    make_is_bicategory.
    - reflexivity.
    - intros ? ? ? [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; cbn in *.
        by path_induction.
    - intros ? ? f g p ; cbn in *.
      induction p ; hott_simpl.
    - intros X Y f g p ; cbn in *.
      induction p ; hott_simpl.
    - intros X Y f g p ; cbn in *.
      induction p ; hott_simpl.
    - intros X Y f g p ; cbn in *.
      induction p ; hott_simpl.
    - intros ; cbn ; hott_simpl.
    - intros ; cbn ; hott_simpl.
    - intros ; cbn ; hott_simpl.
    - intros ; cbn ; hott_simpl.
    - intros ? ? ? ? h₁ h₂ g₁ g₂ f₁ f₂ p q r ; cbn in *.
      induction p, q, r ; hott_simpl.
    - intros ? ? ? ? h₁ h₂ g₁ g₂ f₁ f₂ p q r ; cbn in *.
      induction p, q, r ; hott_simpl.
    - intros ; cbn ; hott_simpl.
    - intros ; cbn ; hott_simpl.
    - intros ; cbn.
      rewrite trianglator.
      hott_simpl.
    - intros ; cbn in *.
      rewrite <- inv_pp.
      rewrite pentagonator.
      rewrite !inv_pp, !ap_V.
      rewrite concat_1p, concat_p1.
      reflexivity.
  Qed.

  Definition SemiSegalType_bicat : BiCategory
    := Build_BiCategory SemiSegalType_bicat_d
                       SemiSegalType_is_bicategory.

  Global Instance locally_univalent_semi_segal_type
    : LocallyUnivalent SemiSegalType_bicat.
  Proof.
    intros X Y ; cbn.
    apply _.
  Defined.

  Definition SemiSegalType_strict
    : IsStrict SemiSegalType_bicat.
  Proof.
    make_strict.
    - exact λ.
    - exact ρ.
    - intros.
      symmetry.
      apply α.
    - intros ; cbn.
      rewrite trianglator.
      hott_simpl.
    - intros ; cbn.
      rewrite <- inv_pp.
      rewrite pentagonator.
      rewrite !inv_pp, !ap_V.
      reflexivity.
    - intros X Y f ; cbn in *.
      induction (λ X Y f).
      reflexivity.
    - intros X Y f ; cbn in *.
      induction (ρ X Y f).
      reflexivity.
    - intros W X Y Z h g f ; cbn in *.
      induction (α W X Y Z h g f).
      reflexivity.
  Defined.

  Definition SemiSegal_21
             `{Funext}
    : is_21 SemiSegalType_bicat.
  Proof.
    intros X Y f g p ; simpl in *.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact p^.
    - apply concat_pV.
    - apply concat_Vp.
  Defined.
End SemiSegalType.