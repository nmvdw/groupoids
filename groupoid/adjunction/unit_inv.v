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

Section UnitInv.
  Context `{Univalence}.

  Definition unit_inv_map (G : groupoid) `{strict_grpd G}
    : @one_cell _ grpd (path_groupoid(gquot_o G)) G.
  Proof.
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
    - reflexivity.
  Defined.

  Definition unit_inv_d
    : LaxTransformation_d
        (lax_comp path_groupoid_functor gquot_functor)
        (lax_id_functor grpd).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - exact unit_inv_map.
    - exact unit_naturality.
  Defined.
End unit.