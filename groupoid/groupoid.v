Require Import HoTT.
From GR Require Import polynomial setoid.

(** * Basic definitions *)
(** A groupoid consists of a relation with a certain structure.
   This relation has two parts.
   First of all, it has objects.
   Second of all, for each pair of objects there is a set of arrows between them.
*)
Definition set_relation (A : Type) := A -> A -> hSet.

(** Now we can define what a groupoid is.
    In addition to a relation, we also have algebraic structure.
*)
Record groupoid (A : Type) :=
  Build_grpd { hom : set_relation A ;
               e : forall (x : A), hom x x ;
               inv : forall (x y : A), hom x y -> hom y x ;
               comp : forall (x y z : A), hom x y -> hom y z -> hom x z ;
               ca : forall (x y z v : A) (p : hom x y) (q : hom y z) (r : hom z v),
                   comp _ _ _ p (comp _ _ _ q r) = comp _ _ _ (comp _ _ _ p q) r ;
               ce : forall (x y : A) (p : hom x y), comp x y y p (e y) = p ;
               ec : forall (x y : A) (p : hom x y), comp x x y (e x) p = p ;
               ci : forall (x y : A) (p : hom x y), comp x y x p (inv x y p) = e x ;
               ic : forall (x y : A) (p : hom x y), comp y x y (inv x y p) p = e y ;
             }.

Arguments e {_} {_} _.
Arguments hom {_} _.
Arguments inv {_} {_} {_} {_}.
Arguments ca {A _ x y z v} p q r.
Arguments ce {A _ x y} p.
Arguments ec {A _ x y} p.
Arguments ci {A _ x y} p.
Arguments ic {A _ x y} p.
Notation "p × q" := (comp _ _ _ _ _ p q) (at level 80).

(** ** Constructions of groupoids *)
(** Now let's discuss some examples of groupoids.
    The first example is the paths on a certain type.
*)
Definition path_space (X : Type) : X -> X -> hSet
  := fun (x y : X) => BuildhSet (Trunc 0 (x = y)).

Definition path_groupoid (X : Type) : groupoid X.
Proof.
  unshelve esplit ; simpl.
  - exact (path_space X).
  - exact (fun _ => tr idpath).
  - exact (fun _ _ => Trunc_rec (fun p => tr p^)).
  - exact (fun _ _ _ p' q' => Trunc_rec (fun p => Trunc_rec (fun q => tr (p @ q)) q') p').
  - intros ? ? ? ? p q r ; simpl.
    strip_truncations ; simpl.
    exact (ap tr (concat_p_pp p q r)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_p1 p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_1p p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_pV p)).
  - intros ? ? p.
    strip_truncations ; simpl.
    exact (ap tr (concat_Vp p)).
Defined.

Notation "p · q" := (comp _ (path_groupoid _) _ _ _ p q) (at level 80).

(** Groupoids are closed under products. *)
Definition prod_groupoid
           {A B : Type} (G₁ : groupoid A) (G₂ : groupoid B)
  : groupoid (A * B).
Proof.
  unshelve esplit.
  - exact (fun x y => BuildhSet (hom G₁ (fst x) (fst y) * hom G₂ (snd x) (snd y))).
  - intros ; simpl.
    split ; apply e.
  - intros ? ? [p1 p2] ; simpl.
    exact (inv p1, inv p2).
  - intros ? ? ? [p1 p2] [q1 q2].
    exact (p1 × q1, p2 × q2).
  - intros ? ? ? ? [p1 p2] [q1 q2] [r1 r2].
    apply path_prod ; apply ca.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ce.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ec.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ci.
  - intros ? ? [p1 p2].
    apply path_prod ; apply ic.
Defined.

(** Groupoids are closed under sums. *)
Definition sum_groupoid
           {A B : Type} (G₁ : groupoid A) (G₂ : groupoid B)
  : groupoid (A + B).
Proof.
  unshelve esplit.
  - exact (fun x y =>
             match x, y with
             | inl x, inl y => hom G₁ x y
             | inl _, inr _ => BuildhSet Empty
             | inr _, inl _ => BuildhSet Empty
             | inr x, inr y => hom G₂ x y
             end).
  - intros [x | x] ; apply e.
  - intros [? | ?] [? | ?] ; contradiction || apply inv.
  - intros [? | ?] [? | ?] [? | ?] ; contradiction || apply comp.
  - intros [? | ?] [? | ?] [? | ?] [? | ?] ; try contradiction ; apply ca.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ce.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ec.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ci.
  - intros [? | ?] [? | ?] ; try contradiction ; apply ic.
Defined.    

(** We can apply polynomial functors to groupoids. *)
Definition lift_groupoid
           {A : Type} (G : groupoid A) (P : polynomial)
  : groupoid (poly_act P A).
Proof.
  induction P ; simpl.
  - exact G.
  - exact (path_groupoid T).
  - apply prod_groupoid ; assumption.
  - apply sum_groupoid ; assumption.
Defined.
    
(** Every setoid induces a groupoid. *)
Definition setoid_to_groupoid
           {A : Type}
           (R : setoid A)
  : groupoid A.
Proof.
  simple refine {| hom := fun a₁ a₂ => BuildhSet (rel R a₁ a₂) ;
                   e := refl ;
                   inv := fun _ _ p => sym p ;
                   comp := fun _ _ _ p q => trans p q
                |}
  ; intros ; simpl ; apply path_ishprop.
Defined.

(** ** Some equational theory for groupoids *)
(** [e⁻¹ = e] *)
Definition inv_e
           {A : Type}
           (G : groupoid A)
           (a : A)
  : inv (@e _ G a) = e a
  := (ce _)^ @ ic (e a).

(** [(g⁻¹)⁻¹ = g] *)
Definition inv_involutive
           {A : Type}
           (G : groupoid A)
           {a₁ a₂ : A}
           (g : hom G a₁ a₂)
  : inv (inv g) = g.
Proof.
  refine ((ce (inv (inv g)))^ @ _).
  refine (ap (fun p => _ × p) (ic g)^ @ _).
  refine (ca _ _ _ @ _).
  refine (ap (fun p => p × _) (ic _) @ _).
  apply ec.
Defined.

(** [(g h)⁻¹ = h⁻¹ g ⁻¹] *)
Definition inv_prod
           {A : Type}
           (G : groupoid A)
           {a₁ a₂ a₃ : A}
           (g₁ : hom G a₁ a₂)
           (g₂ : hom G a₂ a₃)
  : inv (g₁ × g₂) = (inv g₂ × inv g₁).
Proof.
  refine (_ @ (ce (inv g₂ × inv g₁))).
  refine (_ @ ap (fun p => _ × p) (ci (g₁ × g₂))).
  refine (_ @ (ca _ _ _)^).
  refine (_ @ ap (fun p => p × _) (ca (inv g₂ × inv g₁) g₁ g₂)^).
  refine (_ @ ap (fun p => (p × _) × _) (ca (inv g₂) (inv g₁) g₁)).
  refine (_ @ (ap (fun p => ((_ × p) × _) × _) (ic _))^).
  refine (_ @ (ap (fun p => (p × _) × _) (ce _))^).
  refine (_ @ (ap (fun p => p × _) (ic _))^).
  exact (ec _)^.
Defined.


Record groupoid_functor
       {A B : Type}
       (G₁ : groupoid A) (G₂ : groupoid B)
  := { f_obj : A -> B ;
       f_hom : forall (x y : A), hom G₁ x y -> hom G₂ (f_obj x) (f_obj y) ;
       f_e : forall (x : A), f_hom x x (e x) = e (f_obj x) ;
       f_inv : forall (x y : A) (g : hom G₁ x y),
           f_hom y x (inv g) = inv (f_hom x y g) ;
       f_comp : forall (x y z : A) (g₁ : hom G₁ x y) (g₂ : hom G₁ y z),
           f_hom x z (g₁ × g₂) = (f_hom x y g₁ × f_hom y z g₂)
     }.

Arguments f_obj {A B G₁ G₂} _ a.
Arguments f_hom {A B G₁ G₂} _ x y _.
Arguments f_e {A B G₁ G₂ _} x.
Arguments f_inv {A B G₁ G₂ _} _ _ _.
Arguments f_comp {A B G₁ G₂ _} _ _ _ _ _.

Definition transport_e
           {A B : Type}
           {G₁ : groupoid A} {G₂ : groupoid B}
           (F₁ F₂ : groupoid_functor G₁ G₂)
           (eq_obj : f_obj F₁ = f_obj F₂)
           (x : A)
  : hom G₂ (f_obj F₂ x) (f_obj F₁ x)
  := transport (fun h => hom G₂ (f_obj F₂ x) (h x)) eq_obj^ (e _).

Definition compute_transport
           {A B : Type}
           {G₁ : groupoid A} {G₂ : groupoid B}
           (F₁ F₂ : groupoid_functor G₁ G₂)
           (eq_obj : f_obj F₁ = f_obj F₂)
           {x y : A} (g : hom G₁ x y)
  : transport (fun f => hom G₂ (f x) (f y))
              (eq_obj^)
              (f_hom F₂ x y g)
    = ((inv (transport_e F₁ F₂ eq_obj x))
         × f_hom F₂ x y g × transport_e F₁ F₂ eq_obj y).
Proof.
  unfold transport_e.
  destruct F₁, F₂ ; simpl in *.
  induction eq_obj ; simpl in *.
  refine (_ @ (ce _)^).
  refine (_^ @ ap (fun z => z × _) (inv_e _ _)^).
  apply ec.
Defined.

Definition functor_eq
           {A B : Type}
           {G₁ : groupoid A} {G₂ : groupoid B}
           (F₁ F₂ : groupoid_functor G₁ G₂)
           (eq_obj : f_obj F₁ = f_obj F₂)
           (eq_hom : f_hom F₁
                     =
                     fun x y g =>
                       transport (fun f => hom G₂ (f x) (f y))
                                 (eq_obj^)
                                 (f_hom F₂ x y g)
           )
           `{Univalence}
  : F₁ = F₂.
Proof.
  destruct F₁, F₂ ; simpl in *.
  induction eq_obj ; simpl in *.
  induction (eq_hom : f_hom0 = f_hom1) ; simpl in *.
  assert (f_e0 = f_e1) as ->.
  { apply path_ishprop. }
  assert (f_inv0 = f_inv1) as ->.
  { apply path_ishprop. }
  assert (f_comp0 = f_comp1) as ->.
  { apply path_ishprop. }
  reflexivity.
Defined.

Section groupoid_iso.
  Context `{UA : Univalence}.

  Definition pullback
             {A B : Type}
             (f : A -> B)
             (H : groupoid B)
    : groupoid A
    := {| hom := fun a b => hom H (f a) (f b) ;
          e := fun a => e (f a) ;
          inv := fun a b g => inv g ;
          comp := fun a b c g h => g × h ;
          ca := fun x y z v p q r => ca p q r ;
          ce := fun x y p => ce p ;
          ec := fun x y p => ec p ;
          ci := fun x y p => ci p ;
          ic := fun x y p => ic p |}.
    
  (*Definition groupoid_eq
             {A B : Type}
             (G : groupoid A) (H : groupoid B)
             (f : A -> B)
             (p_hom : forall (a b : A), hom G a b -> hom H (f a) (f b))
             (p_e : forall (a : A), p_hom a a (e a) = e (f a))
             (p_i : forall (a b : A) (g : hom G a b),
                 p_hom b a (inv g) = inv (p_hom a b g))
             (p_c : forall (a b c : A) (g : hom G a b) (h : hom G b c),
                 p_hom a c (g × h) = ((p_hom a b g) × (p_hom b c h)))
             `{forall (a b : A), IsEquiv (p_hom a b)}
    : G = pullback f H.
  Proof.
    unfold pullback ; destruct G, H ; simpl in *.
  Admitted.*)
End groupoid_iso.

Section fun_groupoid.
  Variable (A B : Type)
           (G₁ : groupoid A) (G₂ : groupoid B).
  Context `{Funext}.

  Definition f_object : Type
    := groupoid_functor G₁ G₂.

  Definition f_morph : f_object -> f_object -> hSet
    := fun f g => BuildhSet {p : forall (a : A),
                                 hom G₂ (f_obj f a) (f_obj g a) &
                                 forall (x y : A) (h : hom G₁ x y),
                                   f_hom f x y h = (p x × f_hom g x y h × inv (p y))
                            }.

  Definition f_morph_eq
             (x y : f_object)
             (g h : f_morph x y)
    : g.1 = h.1 -> g = h
    := path_sigma_hprop _ _.

  Definition f_eo (x : f_object)
    : f_morph x x.
  Proof.
    simple refine (fun a => e (f_obj x a);_) ; simpl.
    intros a b g.
    refine (ap (fun z => _ × z) (inv_e _ _) @ _)^.
    refine (ce _ @ ec _).
  Defined.

  Definition f_invo (x y : f_object) (g : f_morph x y)
    : f_morph y x.
  Proof.
    simple refine (fun a => inv (g.1 a);_) ; simpl.
    intros a b h.
    refine (ap (fun z => (_ × z) × _) (g.2 a b h) @ _)^.
    refine (ap (fun z => z × _) (ca _ _ _) @ _).
    refine (ap (fun z => (z × _) × _) (ca _ _ _) @ _).
    refine (ap (fun z => ((z × _) × _) × _) (ic _) @ _).
    refine (ap (fun z => (z × _) × _) (ec _) @ _).
    refine ((ca _ _ _)^ @ _).
    refine (ap (fun z => _ × z) (ci _) @ ce _).
  Defined.

  Definition f_concat (x y z : f_object) (g : f_morph x y) (h : f_morph y z)
    : f_morph x z.
  Proof.
    simple refine (fun a => g.1 a × h.1 a;_) ; simpl.
    intros a b p.
    refine (_ @ ap (fun z => _ × z) (inv_prod _ _ _)^).
    refine (_ @ (ca _ _ _)^).
    refine (g.2 a b p @ _).
    refine (ap (fun z => z × inv (g.1 b)) _).
    refine (_ @ ca _ _ _ @ ca _ _ _).
    refine (ap (fun z => g.1 a × z) _).
    refine (_ @ (ca _ _ _)^).
    exact (h.2 a b p).
  Defined.

  Definition fun_groupoid
    : groupoid f_object.
  Proof.
    simple refine {| hom := f_morph ;
                     e := f_eo ;
                     inv := f_invo ;
                     comp := f_concat
                  |}
    ; intros ; apply f_morph_eq ; funext ? ; cbn.
    - apply ca.
    - apply ce.
    - apply ec.
    - apply ci.
    - apply ic.
  Defined.
End fun_groupoid.