Require Import HoTT.
From HoTT.Categories Require Import
     Category.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.examples.one_types
     bicategory.equivalence
     bicategory.adjoint
     lax_functor.lax_functor.
From GR.groupoid Require Import
     groupoid_quotient.gquot
     groupoid_quotient.gquot_functor
     groupoid_quotient.gquot_principles
     grpd_bicategory.grpd_bicategory
     path_groupoid.path_groupoid.
From GR.basics Require Import
     general.

Definition strict_grpd_eq
           `{Univalence}
           (G : groupoid)
           `{strict_grpd G}
           {x y : G}
           (g : hom G x y)
  : x = y
  := @equiv_inv _
                _
                (@Category.idtoiso G.1 x y)
                (@obj_cat G _ x y)
                (Build_Isomorphic (G.2 _ _ g)).

Definition strict_grpd_eq_e
           `{Univalence}
           (G : groupoid)
           `{strict_grpd G}
           (x : G)
  : strict_grpd_eq G (e x) = 1%path.
Proof.
  rewrite <- (@eissect _
                       _
                       (@Category.Morphisms.idtoiso G.1 x x)
                       (@obj_cat G _ x x)).
  unfold strict_grpd_eq.
  apply ap.
  apply path_isomorphic ; cbn.
  reflexivity.
Defined.

Definition strict_grpd_eq_comp
           `{Univalence}
           (G : groupoid)
           `{strict_grpd G}
           {x y z : G}
           (g₁ : hom G x y) (g₂ : hom G y z)
  : strict_grpd_eq G (g₁ · g₂) = strict_grpd_eq G g₁ @ strict_grpd_eq G g₂.
Proof.
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 x z)
                    (@obj_cat G _ x z)
                    (strict_grpd_eq G (g₁ · g₂))
          ).
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 x z)
                    (@obj_cat G _ x z)
                    (strict_grpd_eq G g₁ @ strict_grpd_eq G g₂)
          ).
  apply ap ; simpl.
  apply path_isomorphic.
  rewrite <- (idtoiso_comp G.1 (strict_grpd_eq G g₂) (strict_grpd_eq G g₁)).
  rewrite !eisretr.
  reflexivity.
Defined.

Definition strict_grpd_eq_inv
           `{Univalence}
           (G : groupoid)
           `{strict_grpd G}
           {x y : G}
           (g : hom G x y)
  : strict_grpd_eq G (inv g) = (strict_grpd_eq G g)^.
Proof.
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 y x)
                    (@obj_cat G _ y x)
                    (strict_grpd_eq G (inv g))
          ).
  rewrite <-
          (@eissect _
                    _
                    (@Category.Morphisms.idtoiso G.1 y x)
                    (@obj_cat G _ y x)
                    (strict_grpd_eq G g)^
          ).
  apply ap ; simpl.
  apply path_isomorphic.
  rewrite <- (idtoiso_inv G.1 (strict_grpd_eq G g)).
  rewrite !eisretr.
  reflexivity.
Defined.

Section unit.
  Context `{Univalence}.
  Variable (G : groupoid).

  Definition unit
    : @one_cell _ grpd G (path_groupoid(gquot_o G)).
  Proof.
    cbn.
    simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
    - apply gcl.
    - intros ? ? g ; cbn in *.
      apply (gcleq _ g).
    - intros ? ? ? g₁ g₂ ; cbn in *.
      apply gconcat.
    - intros x ; cbn in *.
      apply ge.
  Defined.

  Definition unit_inv `{strict_grpd G}
    : @one_cell _ grpd (path_groupoid(gquot_o G)) G.
  Proof.
    cbn.
    simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
    - simple refine (gquot_rec _ _ _ _ _ _ _).
      + exact idmap.
      + exact (fun _ _ => strict_grpd_eq G).
      + exact (strict_grpd_eq_e G).
      + exact (fun _ _ => strict_grpd_eq_inv G).
      + exact (fun _ _ _ => strict_grpd_eq_comp G).
    - intros x y p ; simpl.
      induction p.
      apply e.
    - intros x y z p q.
      induction p, q ; simpl.
      symmetry.
      rewrite <- ce ; cbn.
      reflexivity.
    - intros x ; cbn.
      reflexivity.
  Defined.
End unit.

(*
  Definition unit_retr
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
    : is_equivalence counit.
  Proof.
    simple refine {| f_inv := counit_inv ;
                     retr := counit_retr ;
                     sect := counit_sect |}.
  Defined.

  Definition counit_adjunction
    : is_adjunction counit counit_inv.
  Proof.
    simple refine {| unit := _ |}.
    - cbn ; symmetry.
      apply counit_sect.
    - apply counit_retr.
    - unfold bc_whisker_r, bc_whisker_l ; cbn.
      hott_simpl.
      rewrite ap_V.
      rewrite ap_postcompose.
      rewrite <- path_forall_V, <- path_forall_1.
      reflexivity.
    - unfold bc_whisker_r, bc_whisker_l.
      simpl ; hott_simpl.
      rewrite ap_V.
      rewrite ap_precompose.
      rewrite <- !path_forall_V, <- path_forall_1.
      (* apply ap.
      funext x ; revert x.
      simple refine (gquot_ind_prop _ _ _).
      reflexivity. *)
  Admitted.
End counit.
*)