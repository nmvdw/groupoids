Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.univalent
     bicategory.adjoint
     bicategory.equivalence.

Section OneTypesBiCategory.
  Context `{Funext}.
  
  Definition maps (A B : 1 -Type) : PreCategory.
  Proof.
    simple refine (@Build_PreCategory (A -> B) (fun f g => f = g) _ _ _ _ _ _).
    - reflexivity.
    - intros ? ? ? p q ; exact (q @ p).
    - cbn ; intros.
      apply concat_p_pp.
    - cbn ; intros.
      apply concat_p1.
    - cbn ; intros.
      apply concat_1p.
  Defined.

  Definition maps_cat (A B : 1 -Type) : IsCategory (maps A B).
  Proof.
    intros f g ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros p ; induction p.
      reflexivity.
  Defined.
  
  Definition one_types_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact (1 -Type).
    - exact (fun X Y => maps X Y).
    - exact (fun _ => idmap).
    - exact (fun _ _ _ p => Datatypes.fst p o Datatypes.snd p)%function.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [p₁ p₂] ; cbn in *.
      funext x.
      exact (ap10 p₁ (f₂ x) @ ap g₁ (ap10 p₂ x)).
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros X Y f ; simpl in *.
      reflexivity.
    - intros W X Y Z f g h ; simpl in *.
      reflexivity.
    - intros W X Y Z f g h ; simpl in *.
      reflexivity.
  Defined.

  Definition one_types_is_bicategory : is_bicategory one_types_d.
  Proof.
    make_is_bicategory.
    - intros X Y Z [f₁ f₂] ; simpl in *.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y Z [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; simpl in *.
      induction p₁, p₂, q₁, q₂ ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - intros X Y f g p ; simpl in *.
      induction p ; simpl.
      rewrite path_forall_1.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ph pg pf ; simpl in *.
      induction ph, pg, pf ; simpl.
      rewrite !path_forall_1.
      reflexivity.
    - intros W X Y Z h₁ h₂ g₁ g₂ f₁ f₂ ph pg pf ; simpl in *.
      induction ph, pg, pf ; simpl.
      rewrite !path_forall_1.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - intros X Y Z g f ; simpl in *.
      rewrite path_forall_1.
      reflexivity.
    - intros V W X Y Z k h g f ; simpl in *.
      rewrite path_forall_1.
      reflexivity.
  Qed.

  Definition one_types : BiCategory
    := Build_BiCategory one_types_d one_types_is_bicategory.

  Definition one_types_is_21
    : is_21 one_types.
  Proof.
    intros X Y f g p ; simpl in *.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - exact p^.
    - apply concat_pV.
    - apply concat_Vp.
  Defined.
  
  Global Instance locally_univalent_one_types
    : LocallyUnivalent one_types.
  Proof.
    intro ; apply _.
  Qed.
  
  Definition one_types_equiv_to_adjequiv_d
             {X Y : one_types}
             (f : X <~> Y)
    : @is_left_adjoint_d one_types _ _ f.
  Proof.
    make_is_left_adjoint.
    - exact (f^-1)%equiv.
    - funext x ; cbn.
      symmetry.
      apply eissect.
    - funext x ; cbn.
      apply eisretr.
  Defined.

  Definition one_types_equiv_to_adjequiv_is_adj
             {X Y : one_types}
             (f : X <~> Y)
    : is_adjunction (one_types_equiv_to_adjequiv_d f).
  Proof.
    make_is_adjunction ; cbn.
    - rewrite !concat_p1, !concat_1p.
      rewrite <- path_forall_pp.
      rewrite <- path_forall_1.
      f_ap.
      funext x.
      rewrite concat_1p, !ap10_path_forall, concat_p1 ; cbn.
      rewrite other_adj.
      rewrite <- ap_V, <- ap_pp.
      rewrite concat_Vp ; simpl.
      reflexivity.
    - rewrite !concat_p1, !concat_1p.
      rewrite <- path_forall_pp.
      rewrite <- path_forall_1.
      f_ap.
      funext x.
      rewrite concat_1p, !ap10_path_forall, concat_p1 ; cbn.
      rewrite eisadj.
      rewrite <- ap_pp.
      rewrite concat_Vp ; simpl.
      reflexivity.
  Qed.
  
  Definition one_types_equiv_to_adjequiv
             {X Y : one_types}
             (f : X <~> Y)
    : X ≃ Y.
  Proof.
    simple refine (@Build_adjoint_equivalence one_types X Y f _ _ _).
    - exact (Build_is_left_adjoint
               (one_types_equiv_to_adjequiv_d f)
               (one_types_equiv_to_adjequiv_is_adj f)).
    - apply one_types_is_21.
    - apply one_types_is_21.
  Defined.

  Lemma path_adjequiv
        {X Y : one_types}
        {f g : X ≃ Y}
    : f.1 = g.1 -> f = g.
  Proof.
    destruct f as [f Hf], g as [g Hg]. simpl.
    intros p.
  Admitted.
  
  Lemma equiv_to_adjequiv_path
        {X Y : one_types}
        (p : X = Y)
    : one_types_equiv_to_adjequiv (equiv_path X Y (ap _ p)) = id_to_adjequiv X Y p.
  Proof.
    induction p ; cbn.
    apply path_adjequiv ; cbn.
    reflexivity.
  Qed.

  Instance one_types_equivalence 
        (X Y : one_types)
        (f : one_types⟦X,Y⟧)
    : is_equivalence f -> IsEquiv f.
  Proof.
    intros Hf.
    simple refine (isequiv_adjointify _ _ _ _).
    - apply (equiv_inv Hf).
    - intros y.
      pose (fr := retr f Hf).
      exact (ap10 fr y).
    - intros x.
      pose (fs := sect f Hf).
      exact (ap10 fs x).
  Defined.

  Instance isequiv_one_types_equiv_to_adjequiv
           (X Y : one_types)
    : IsEquiv (@one_types_equiv_to_adjequiv X Y).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros HXY ; cbn in *.
      apply adjoint_equivalent_equivalence in HXY.
      pose (f := equiv_morph HXY) ; cbn in *.
      exists f.
      apply one_types_equivalence.
      apply HXY.
    - intros α ; simpl.
      apply path_adjequiv ; cbn.
      reflexivity.
    - intros p.
      apply path_equiv ; cbn.
      reflexivity.
  Defined.
  
  Global Instance univalent_0_one_types `{Univalence}
    : Univalent_0 one_types.
  Proof.
    intros X Y.
    eapply @isequiv_homotopic; [ | intro; apply equiv_to_adjequiv_path ].
    change (IsEquiv (one_types_equiv_to_adjequiv o (equiv_path X Y o ap trunctype_type))).
    (* TODO: typeclasses eauto doesn't work here *)
    eapply (@isequiv_compose _ _ (equiv_path X Y o ap trunctype_type)).
    - change (IsEquiv (equiv_path X Y o ap trunctype_type)).
      eapply (@isequiv_compose _ _ (ap trunctype_type)); typeclasses eauto.
    - apply _.
  Defined.
End OneTypesBiCategory.
