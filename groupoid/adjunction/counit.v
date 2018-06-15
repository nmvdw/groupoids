Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.examples.one_types
     bicategory.equivalence
     bicategory.adjoint
     lax_functor.lax_functor
     lax_functor.examples.identity
     lax_functor.examples.composition
     lax_transformation.lax_transformation.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid.
From GR.basics Require Import
     general.

Section counit.
  Context `{Univalence}.
  Variable (A : 1 -Type).

  Definition counit
    : @one_cell _ one_types (gquot_o(path_groupoid A)) A.
  Proof.
    cbn.
    simple refine (gquot_rec A _ _ _ _ _ _) ; cbn.
    - exact idmap.
    - exact (fun _ _ => idmap).
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Defined.

  Definition counit_inv
    : @one_cell _ one_types A (gquot_o(path_groupoid A))
    := gcl (path_groupoid A).

  Definition counit_retr
    : @two_cell _ one_types _ _ (counit ⋅ counit_inv)%bicategory (id_m _)
    := idpath.

  Definition counit_sect
    : @two_cell _ one_types _ _ (counit_inv ⋅ counit)%bicategory (id_m _).
  Proof.
    funext x ; revert x.
    simple refine (gquot_ind_set _ _ _ _).
    - reflexivity.
    - intros ? ? g.
      apply map_path_over.
      apply path_to_square.
      refine (concat_p1 _ @ _ @ (concat_1p _)^) ; cbn in *.
      refine (_ @ (ap_idmap _)^).
      refine (ap_compose counit _ _ @ _).
      refine (ap _ (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _) @ _).
      induction g ; simpl.
      exact (ge _ _)^.
  Defined.

  Global Instance counit_sect_iso
    : IsIsomorphism counit_sect.
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - symmetry.
      apply counit_sect.
    - apply concat_pV.
    - apply concat_Vp.
  Defined.

  Definition counit_equivalence
    : is_equivalence counit
    := {| f_inv := counit_inv ;
          retr := counit_retr ;
          sect := counit_sect |}.

  Definition counit_adjunction
    : is_adjunction counit counit_inv.
  Proof.
    simple refine {| unit := _ |}.
    - cbn ; symmetry.
      apply counit_sect.
    - apply counit_retr.
    - unfold bc_whisker_r, bc_whisker_l ; simpl.
      rewrite concat_1p, !concat_p1, ap_V.
      rewrite ap_postcompose.
      rewrite <- path_forall_V, <- path_forall_1.
      reflexivity.
    - apply Morphisms.iso_moveR_pV.
      unfold bc_whisker_r, bc_whisker_l.
      rewrite !left_identity.
      apply Morphisms.iso_moveR_Vp.
      simpl.      
      rewrite !concat_1p, ap_V.
      rewrite ap_precompose.
      rewrite <- path_forall_V, <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      reflexivity.
  Defined.
End counit.

Definition naturality_help
           `{Univalence}
           {X Y : one_types}
           (f : X -> Y)
           {a₁ a₂ : path_groupoid X}
           (g : hom (path_groupoid X) a₁ a₂)
  : path_over
      (fun g0 : gquot (path_groupoid X) =>
         f (counit X g0)
         =
         counit Y ((Fmor (lax_comp gquot_functor path_groupoid_functor)) f g0))
      (gcleq (path_groupoid X) g)
      idpath
      idpath.
Proof.
  apply map_path_over.
  simple refine (whisker_square
                   idpath
                   (ap (ap f) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^
                    @ (ap_compose _ _ _)^)
                   _
                   idpath
                   _).
  - exact (ap f g).
  - refine (_ @ (ap_compose _ _ _)^).
    refine ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^ @ _).
    apply ap.
    exact ((gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _)^).
  - apply vrefl.
Qed.

Definition naturality_of_counit `{Univalence} {X Y : one_types} (f : X -> Y)
  : forall (x : gquot (path_groupoid X)),
    f (counit X x)
    =
    counit Y (Fmor (lax_comp gquot_functor path_groupoid_functor) f x).
Proof.
  simple refine (gquot_ind_set _ _ _ _).
  - reflexivity.
  - intros a₁ a₂ g.
    exact (naturality_help f g).
Defined.

Definition counit_naturality
           `{Univalence}
           (X Y : one_types)
  : NaturalTransformation
      (precomp (counit X) ((lax_id_functor one_types) Y) o Fmor (lax_id_functor one_types))
      (postcomp (counit Y) ((lax_comp gquot_functor path_groupoid_functor) X)
                o Fmor (lax_comp gquot_functor path_groupoid_functor)).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros f.
    funext x.
    exact (naturality_of_counit f x).
  - intros f g p.
    induction p.
    rewrite !identity_of, left_identity, !right_identity.
    reflexivity.
Defined.

Definition kek `{Univalence} (X : 1 -Type)
  : forall x : gquot (path_groupoid X),
    naturality_of_counit idmap x =
    ap (counit X)
       ((gquot_functorial_idmap (path_groupoid X) x)
          @ gquot_functorial_natural (path_groupoid_map_id X) x).
Proof.
  simple refine (gquot_ind_prop _ _ _).
  intro a.
  Opaque naturality_of_counit gquot_functorial_natural gquot_functorial_idmap.
  simpl.
  rewrite ap_pp.
  rewrite concat_1p.
  Transparent naturality_of_counit gquot_functorial_natural.
  assert (gquot_functorial_natural (path_groupoid_map_id X) (gcl (path_groupoid X) a)
          =
          gcleq _ (e a)) as ->.
  { reflexivity. }
  rewrite ge.
  reflexivity.
Defined.

Definition test `{Univalence}
  : LaxTransformation
      (lax_comp gquot_functor path_groupoid_functor)
      (lax_id_functor one_types).
Proof.
  simple refine {| laxcomponent_of := _ |}.
  - exact counit.
  - apply counit_naturality.
  - intros X.
    simpl.
    repeat refine (_ @ (concat_1p _)^).
    unfold hcomp.
    simpl.
    refine (concat_1p _ @ _).
    unfold lax_comp_id.
    cbn.
    unfold gquot_id.
    refine (_ @ ap _ (path_forall_pp _ _ _ _ _)).
    refine (_ @ (ap_precompose _ _)^).
    apply ap.
    funext x ; revert x.
    exact (kek X).
  - intros X Y Z f g.
    (* simpl.
    unfold hcomp.
    rewrite identity_of.
    rewrite !concat_1p.*)
Admitted.