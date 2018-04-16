Require Import HoTT.
From GR Require Import path_over globe_over.

Definition path_fam (A : Type)
  := {x : A & {y : A & (x = y) * (x = y)}}.

Definition lpath {A : Type} (p : path_fam A)
  := fst (p.2.2).

Definition rpath {A : Type} (p : path_fam A)
  := snd (p.2.2).

Module Export path_coeq.
  Private Inductive pCoeq {A B : Type} (P : B -> path_fam A) :=
  | pcoeq : A -> pCoeq P.

  Axiom pcp : forall {A B : Type}
                     {P : B -> path_fam A}
                     (b : B),
      globe (ap (pcoeq P) (lpath (P b))) (ap (pcoeq P) (rpath (P b))).

  Section pcoeq_ind.
    Variable (A B : Type)
             (P : B -> path_fam A)
             (Y : pCoeq P -> Type)
             (pcoeqY : forall (a : A), Y(pcoeq P a))
             (pcpY : forall (b : B),
                 globe_over Y
                            (pcp b)
                            (path_over_compose (pcoeq P) (apd_po pcoeqY (lpath (P b))))
                            (path_over_compose (pcoeq P) (apd_po pcoeqY (rpath (P b))))).

    Fixpoint pCoeq_ind (x : pCoeq P) : Y x
      := (match x with
          | pcoeq a => fun _ => pcoeqY a
          end) pcpY.
  End pcoeq_ind.
End path_coeq.