Require Import HoTT.
From HoTT.Categories Require Import Category GroupoidCategory Functor FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory examples.cat examples.full_sub.
From GR Require Import polynomial setoid.

(** * Basic definitions *)
Definition groupoid := {C : PreCategory & IsGroupoid C}.

Definition under (G : groupoid) : Type
  := object G.1.

Definition hom (G : groupoid) : under G -> under G -> hSet
  := fun x y => BuildhSet (morphism G.1 x y).

Definition e {G : groupoid} (x : under G) : hom G x x
  := Category.identity x.

Definition comp {G : groupoid} {x y z : under G}
  : hom G x y -> hom G y z -> hom G x z
  := fun g h => @Category.compose G.1 x y z h g.

Notation "p · q" := (comp p q) (at level 40).

Definition inv {G : groupoid} {x y : under G}
  : hom G x y -> hom G y x
  := fun g => @morphism_inverse _ _ _ g (G.2 x y g).

Definition cal
           {G : groupoid}
           {v x y z : under G}
           (p : hom G v x) (q : hom G x y) (r : hom G y z)
  : (p · q) · r = p · (q · r)
  := (associativity G.1 v x y z p q r)^.

Definition car
           {G : groupoid}
           {v x y z : under G}
           (p : hom G v x) (q : hom G x y) (r : hom G y z)
  : p · (q · r) = (p · q) · r
  := associativity G.1 v x y z p q r.

Definition ce
           {G : groupoid}
           {x y : under G}
           (p : hom G x y)
  : p · e y = p
  := left_identity G.1 x y p.

Definition ec
           {G : groupoid}
           {x y : under G}
           (p : hom G x y)
  : e x · p = p
  := right_identity G.1 x y p.

Definition ci
           {G : groupoid}
           {x y : under G}
           (p : hom G x y)
  : p · inv p = e x
  := @left_inverse G.1 x y p (G.2 x y p).

Definition ic
           {G : groupoid}
           {x y : under G}
           (p : hom G x y)
  : inv p · p = e y
  := @right_inverse G.1 x y p (G.2 x y p).

Definition Build_grpd
           (obj : Type)
           (hom : obj -> obj -> hSet)
           (e : forall (x : obj), hom x x)
           (inv : forall {x y : obj}, hom x y -> hom y x)
           (comp : forall {x y z : obj}, hom x y -> hom y z -> hom x z)
           (assoc : forall (x y z v : obj) (p : hom v x) (q : hom x y) (r : hom y z),
               comp p (comp q r) = comp (comp p q) r)
           (ec : forall (x y : obj) (p : hom x y),
               comp (e x) p = p)
           (ce : forall (x y : obj) (p : hom x y),
               comp p (e y) = p)
           (ic : forall (x y : obj) (p : hom x y),
               comp (inv p) p = e y)
           (ci : forall (x y : obj) (p : hom x y),
               comp p (inv p) = e x)
  : groupoid.
Proof.
  simple refine (_;_).
  - simple refine (@Build_PreCategory
                     obj
                     hom
                     e
                     (fun _ _ _ p q => comp _ _ _ q p) _ _ _ _).
    + cbn ; intros.
      apply assoc.
    + cbn ; intros.
      apply ce.
    + cbn ; intros.
      apply ec.
  - intros x y p ; cbn in *.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _) ; cbn.
    + exact (inv _ _ p).
    + apply ci.
    + apply ic.
Defined.

(** ** Some equational theory for groupoids *)
(** [e⁻¹ = e] *)
Definition inv_e
           {G : groupoid}
           (a : under G)
  : inv (@e G a) = e a
  := (ce _)^ @ ic (e a).

(** [(g⁻¹)⁻¹ = g] *)
Definition inv_involutive
           {G : groupoid}
           {a₁ a₂ : under G}
           (g : hom G a₁ a₂)
  : inv (inv g) = g.
Proof.
  refine ((ce (inv (inv g)))^ @ _).
  refine (ap (fun p => _ · p) (ic g)^ @ _).
  refine (car _ _ _ @ _).
  refine (ap (fun p => p · _) (ic _) @ _).
  apply ec.
Defined.

(** [(g h)⁻¹ = h⁻¹ g ⁻¹] *)
Definition inv_prod
           {G : groupoid}
           {a₁ a₂ a₃ : under G}
           (g₁ : hom G a₁ a₂)
           (g₂ : hom G a₂ a₃)
  : inv (g₁ · g₂) = inv g₂ · inv g₁.
Proof.
  refine (_ @ (ce (inv g₂ · inv g₁))).
  refine (_ @ ap (fun p => _ · p) (ci (g₁ · g₂))).
  refine (_ @ cal _ _ _).
  refine (_ @ ap (fun p => p · _) (car (inv g₂ · inv g₁) g₁ g₂)^).
  refine (_ @ ap (fun p => (p · _) · _) (car (inv g₂) (inv g₁) g₁)).
  refine (_ @ (ap (fun p => ((_ · p) · _) · _) (ic _))^).
  refine (_ @ (ap (fun p => (p · _) · _) (ce _))^).
  refine (_ @ (ap (fun p => p · _) (ic _))^).
  exact (ec _)^.
Defined.

(** Groupoid functors *)
Definition grpd_functor `{Univalence} (G₁ G₂ : groupoid) : PreCategory
  := functor_category G₁.1 G₂.1.

Definition grpd_object_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : under G₁ -> under G₂
  := object_of F.

Definition grpd_morphism_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y : under G₁},
    hom G₁ x y -> hom G₂ (grpd_object_of F x) (grpd_object_of F y)
  := morphism_of F.

Definition grpd_identity_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall (x : under G₁), grpd_morphism_of F (e x) = e (grpd_object_of F x)
  := identity_of F.

Definition grpd_composition_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y z : under G₁} (p : hom G₁ x y) (q : hom G₁ y z),
    grpd_morphism_of F (p · q) = grpd_morphism_of F p · grpd_morphism_of F q
  := composition_of F.

Definition grpd_inverse_of `{Univalence} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y : under G₁} (p : hom G₁ x y),
    grpd_morphism_of F (inv p) = inv (grpd_morphism_of F p).
Proof.
  intros x y p.
  apply iso_moveL_1V.
  refine (((grpd_composition_of F p (inv p))^ @ _ @ grpd_identity_of F x)).
  apply (ap (grpd_morphism_of F)).
  apply ci.
Defined.

Definition grpd `{Univalence} : BiCategory
  := full_sub Cat (fun C => BuildhProp (IsGroupoid C)).

Definition grpd_obj `{Univalence} : Obj grpd = groupoid
  := idpath.

Definition grpd_hom `{Univalence} : Hom grpd = grpd_functor
  := idpath.

(** ** Constructions of groupoids *)
(** Now let's discuss some examples of groupoids.
    The first example is the paths on a certain type.
*)
Definition path_space (X : Type) : X -> X -> hSet
  := fun (x y : X) => BuildhSet (Trunc 0 (x = y)).

Definition path_groupoid (X : Type) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact X.
  - exact (path_space X).
  - exact (fun _ => tr idpath).
  - exact (fun _ _ => Trunc_rec (fun p => tr p^)).
  - exact (fun _ _ _ p' q' => Trunc_rec (fun p => Trunc_rec (fun q => tr (p @ q)) q') p').
  - intros ? ? ? ? p q r ; simpl.
    strip_truncations ; simpl.
    exact (ap tr (concat_p_pp p q r)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_1p p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_p1 p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_Vp p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_pV p)).
Defined.

(** Groupoids are closed under products. *)
Definition prod_groupoid (G₁ G₂ : groupoid) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact (under G₁ * under G₂).
  - exact (fun x y => BuildhSet (hom G₁ (fst x) (fst y) * hom G₂ (snd x) (snd y))).
  - intros ; simpl.
    split ; apply e.
  - intros ? ? [p1 p2] ; simpl.
    exact (inv p1, inv p2).
  - intros ? ? ? [p1 p2] [q1 q2].
    exact (p1 · q1, p2 · q2).
  - intros ? ? ? ? [p1 p2] [q1 q2] [r1 r2].
    apply path_prod ; apply car.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ec.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ce.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ic.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ci.
Defined.

(** Groupoids are closed under sums. *)
Definition sum_groupoid (G₁ G₂ : groupoid) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact (under G₁ + under G₂).
  - intros [x | x] [y | y].
    + exact (hom G₁ x y).
    + exact (BuildhSet Empty).
    + exact (BuildhSet Empty).
    + exact (hom G₂ x y).
  - intros [x | x] ; apply e.
  - intros [? | ?] [? | ?] ; contradiction || apply inv.
  - intros [? | ?] [? | ?] [? | ?] ; contradiction || apply comp.
  - intros [? | ?] [? | ?] [? | ?] [? | ?] ; try contradiction ; apply car.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ec.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ce.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ic.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ci.
Defined.    

(** We can apply polynomial functors to groupoids. *)
Definition lift_groupoid (G : groupoid) (P : polynomial) : groupoid.
Proof.
  induction P ; simpl.
  - exact G.
  - exact (path_groupoid T).
  - apply prod_groupoid ; assumption.
  - apply sum_groupoid ; assumption.
Defined.
    
(** Every setoid induces a groupoid. *)
Definition setoid_to_groupoid (R : setoid) : groupoid.
Proof.
  simple refine (Build_grpd _ _ _ _ _ _ _ _ _ _) ; simpl.
  - exact (setoid.under R).
  - exact (fun a₁ a₂ => BuildhSet (rel R a₁ a₂)).
  - exact refl.
  - exact (@sym R).
  - exact (@trans R).
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
  - cbn ; intros.
    apply path_ishprop.
Defined.

Section fun_groupoid.
  Variable (G₁ G₂ : groupoid).
  Context `{Univalence}.

  Definition f_object : Type
    := grpd_functor G₁ G₂.

  Definition f_morph : f_object -> f_object -> hSet
    := fun f g => BuildhSet {p : forall (a : under G₁),
                                 hom G₂ (grpd_object_of f a) (grpd_object_of g a) &
                                 forall (x y : under G₁) (h : hom G₁ x y),
                                   grpd_morphism_of f h
                                   = p x · grpd_morphism_of g h · inv (p y)
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
    refine (ap (fun z => _ · z) (inv_e _) @ _)^.
    refine (ce _ @ ec _).
  Defined.

  Definition f_invo (x y : f_object) (g : f_morph x y)
    : f_morph y x.
  Proof.
    simple refine (fun a => inv (g.1 a);_) ; simpl.
    intros a b h.
    refine (ap (fun z => (_ · z) · _) (g.2 a b h) @ _)^.
    refine (ap (fun z => z · _) (car _ _ _) @ _).
    refine (ap (fun z => (z · _) · _) (car _ _ _) @ _).
    refine (ap (fun z => ((z · _) · _) · _) (ic _) @ _).
    refine (ap (fun z => (z · _) · _) (ec _) @ _).
    refine ((car _ _ _)^ @ _).
    refine (ap (fun z => _ · z) (ci _) @ ce _).
  Defined.

  Definition f_concat (x y z : f_object) (g : f_morph x y) (h : f_morph y z)
    : f_morph x z.
  Proof.
    simple refine (fun a => g.1 a · h.1 a;_) ; simpl.
    intros a b p.
    refine (_ @ ap (fun z => _ · z) (inv_prod _ _)^).
    refine (_ @ cal _ _ _).
    refine (g.2 a b p @ _).
    refine (ap (fun z => z · inv (g.1 b)) _).
    refine (_ @ car _ _ _ @ car _ _ _).
    refine (ap (fun z => g.1 a · z) _).
    refine (_ @ cal _ _ _).
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
    - apply car.
    - apply ec.
    - apply ce.
    - apply ic.
    - apply ci.
  Defined.
End fun_groupoid.
