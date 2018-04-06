Require Import HoTT.
From GR Require Import groupoid path_over globe_over.

Module Export gquot.
  Private Inductive gquot {A : Type} (G : groupoid A) :=
  | gcl : A -> gquot G.

  Arguments gcl {_} _ _.

  Axiom geqcl
    : forall {A : Type} (G : groupoid A) {a₁ a₂ : A} (g : hom G a₁ a₂),
      gcl G a₁ = gcl G a₂.

  Axiom ge
    : forall {A : Type} (G : groupoid A) (a : A),
      geqcl G (e a) = idpath.

  Axiom ginv
    : forall {A : Type} (G : groupoid A) {a₁ a₂ : A} (g : hom G a₁ a₂),
      geqcl G (inv g) = (geqcl G g)^.

  Axiom gconcat
    : forall {A : Type} (G : groupoid A)
             {a₁ a₂ a₃ : A}
             (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
      geqcl G (g₁ × g₂) = geqcl G g₁ @ geqcl G g₂.
  
  Axiom gtrunc
    : forall {A : Type} (G : groupoid A), IsTrunc 1 (gquot G).

  Section gquot_ind.
    Variable (A : Type)
             (G : groupoid A)
             (Y : gquot G -> Type)
             (gclY : forall (a : A), Y(gcl G a))
             (geqclY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 path_over Y (geqcl G g) (gclY a₁) (gclY a₂))
             (geY : forall (a : A), globe_over Y
                                                (path_to_globe (ge G a))
                                                (geqclY a a (e a))
                                                (path_over_id (gclY a)))
             (ginvY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 globe_over Y
                            (path_to_globe (ginv G g))
                            (geqclY a₂ a₁ (inv g))
                            (path_over_inv (geqclY a₁ a₂ g)))
             (gconcatY : forall (a₁ a₂ a₃ : A)
                                (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
                 globe_over Y
                            (path_to_globe (gconcat G g₁ g₂))
                            (geqclY a₁ a₃ (g₁ × g₂))
                            (path_over_concat (geqclY a₁ a₂ g₁)
                                              (geqclY a₂ a₃ g₂)))
             (truncY : forall (x : gquot G), IsTrunc 1 (Y x)).

    Fixpoint gquot_ind (g : gquot G) : Y g
      := (match g with
         | gcl a => fun _ _ _ _ _ => gclY a
          end) geqclY geY ginvY gconcatY truncY.

    Axiom gquot_beta_geqclY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
        apd_po gquot_ind (geqcl G g)
        =
        geqclY a₁ a₂ g.
  End gquot_ind.

  Section gquot_rec.
    Variable (A : Type)
             (G : groupoid A)
             (Y : Type)
             (gclY : A -> Y)
             (geqclY : forall (a₁ a₂ : A),
                 hom G a₁ a₂ -> gclY a₁ = gclY a₂)
             (geY : forall (a : A), geqclY _ _ (e a) = idpath)
             (ginvY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 geqclY a₂ a₁ (inv g) = (geqclY a₁ a₂ g)^)
             (gconcatY : forall (a₁ a₂ a₃: A) (g₁: hom G a₁ a₂) (g₂: hom G a₂ a₃),
                 geqclY _ _ (g₁ × g₂) = geqclY _ _ g₁ @ geqclY _ _ g₂)
             (truncY : IsTrunc 1 Y).

    Definition gquot_rec : gquot G -> Y.
    Proof.
      simple refine (gquot_ind A G (fun _ => Y)
                               gclY
                               (fun a₁ a₂ g => const_path_over (geqclY a₁ a₂ g))
                               (fun a => const_globe_over
                                           (path_to_globe (ge G a))
                                           (geqclY a a (e a))
                                           idpath
                                           (path_to_globe (geY a)))
                               _ _ _) ; cbn.
      - intros a₁ a₂ g.
        simple refine (globe_over_whisker
                         (fun _ => Y)
                         _
                         idpath
                         (const_path_over_inv _)
                         (const_globe_over
                            (path_to_globe (ginv G g))
                            (geqclY a₂ a₁ (inv g))
                            ((geqclY a₁ a₂ g)^)
                            (path_to_globe (ginvY a₁ a₂ g))
                         )
                      ).
      - intros a₁ a₂ a₃ g₁ g₂.
        simple refine (globe_over_whisker
                         (fun _ => Y)
                         _
                         idpath
                         (const_path_over_concat _ _)
                         (const_globe_over
                            (path_to_globe (gconcat G g₁ g₂))
                            (geqclY a₁ a₃ (g₁ × g₂))
                            (geqclY a₁ a₂ g₁ @ geqclY a₂ a₃ g₂)
                            (path_to_globe (gconcatY a₁ a₂ a₃ g₁ g₂))
                         )
                      ).
    Defined.
  End gquot_rec.
End gquot.

Arguments gquot_ind {A G} Y gclY geqclY geY ginvY gconcatY truncY.
Arguments gquot_rec {A G}.