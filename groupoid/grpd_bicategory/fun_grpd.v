Require Import HoTT.
From HoTT.Categories Require Import
     Category.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory grpd_laws.

Section fun_groupoid.
  Variable (G₁ G₂ : groupoid).
  Context `{Univalence}.

  Definition f_object : Type
    := grpd_functor G₁ G₂.

  Definition f_morph : f_object -> f_object -> hSet
    := fun f g => BuildhSet {p :
                               forall (a : G₁),
                                 G₂ (grpd_object_of f a) (grpd_object_of g a) &
                                 forall (x y : G₁) (h : G₁ x y),
                                   grpd_morphism_of f h
                                   =
                                   p x ● grpd_morphism_of g h ● inv (p y)
                            }.

  Definition f_morph_eq
             (x y : f_object)
             (g h : f_morph x y)
    : g.1 = h.1 -> g = h
    := path_sigma_hprop _ _.

  Definition f_eo (x : f_object)
    : f_morph x x.
  Proof.
    simple refine (fun a => e (grpd_object_of x a);_) ; simpl.
    intros a b g.
    refine (ap (fun z => _ ● z) (inv_e _) @ _)^.
    exact (grpd_right_identity _ @ grpd_left_identity _).
  Defined.

  Definition f_invo (x y : f_object) (g : f_morph x y)
    : f_morph y x.
  Proof.
    simple refine (fun a => inv (g.1 a);_) ; simpl.
    intros a b h.
    refine (ap (fun z => (_ ● z) ● _) (g.2 a b h) @ _)^.
    refine (ap (fun z => z ● _) (grpd_right_assoc _ _ _) @ _).
    refine (ap (fun z => (z ● _) ● _) (grpd_right_assoc _ _ _) @ _).
    refine (ap (fun z => ((z ● _) ● _) ● _) (grpd_left_inverse _) @ _).
    refine (ap (fun z => (z ● _) ● _) (grpd_left_identity _) @ _).
    refine ((grpd_right_assoc _ _ _)^ @ _).
    refine (ap (fun z => _ ● z) (grpd_right_inverse _) @ grpd_right_identity _).
  Defined.

  Definition f_concat (x y z : f_object) (g : f_morph x y) (h : f_morph y z)
    : f_morph x z.
  Proof.
    simple refine (fun a => g.1 a ● h.1 a;_) ; simpl.
    intros a b p.
    refine (_ @ ap (fun z => _ ● z) (inv_prod _ _)^).
    refine (_ @ grpd_left_assoc _ _ _).
    refine (g.2 a b p @ _).
    refine (ap (fun z => z ● inv (g.1 b)) _).
    refine (_ @ grpd_right_assoc _ _ _ @ grpd_right_assoc _ _ _).
    refine (ap (fun z => g.1 a ● z) _).
    refine (_ @ grpd_left_assoc _ _ _).
    exact (h.2 a b p).
  Defined.

  Definition fun_groupoid : groupoid.
  Proof.
    simple refine (Build_grpd
                     f_object
                     f_morph
                     f_eo
                     f_invo
                     f_concat
                     _ _ _ _ _)
    ; intros ; apply f_morph_eq ; funext ? ; cbn.
    - apply grpd_right_assoc.
    - apply grpd_left_identity.
    - apply grpd_right_identity.
    - apply grpd_left_inverse.
    - apply grpd_right_inverse.
  Defined.
End fun_groupoid.
