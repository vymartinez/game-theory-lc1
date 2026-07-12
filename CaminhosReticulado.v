(** * Equivalência entre caminhos em uma grade cartesiana (lattice paths)

    Disciplina : Lógica Computacional 1, 2026/1
    Autores: Victor Yan Martinez de Ávila, Matrícula: 241032994 / Pedro do Nascimento Holanda, Matrícula: 232005998

    Um caminho é uma lista de passos Right (direita) e Up (cima). Dois caminhos
    são equivalentes quando um é permutação do outro. Provamos que caminhos
    equivalentes têm o mesmo comprimento e o mesmo ponto final. *)

From Stdlib Require Import List.
From Stdlib Require Import Permutation.
Import ListNotations.

(** Passos e caminhos*)
(* ========================================================================= *)

(* Um passo é um movimento elementar: direita ou cima. *)
Inductive passo : Type :=
  | Right : passo
  | Up    : passo.

(* Um caminho é uma sequência (lista) de passos. *)
Definition caminho := list passo.

(* Os dois caminhos que ligam (0,0) a (1,1). *)
Definition c_RU : caminho := [Right; Up].
Definition c_UR : caminho := [Up; Right].

(** Pontos da grade e o efeito de um caminho*)
(* ========================================================================= *)

(* Um ponto é um par (x, y) de naturais. *)
Definition ponto := (nat * nat)%type.

(* Ponto de partida convencional. *)
Definition origem : ponto := (0, 0).

(* Move um ponto por um passo: Right soma em x, Up soma em y. *)
Definition aplica_passo (p : passo) (pt : ponto) : ponto :=
  match p with
  | Right => (fst pt + 1, snd pt)
  | Up    => (fst pt, snd pt + 1)
  end.

(* Ponto alcançado ao percorrer o caminho a partir de pt (recursão na lista). *)
Fixpoint destino (pt : ponto) (c : caminho) : ponto :=
  match c with
  | []      => pt
  | p :: c' => destino (aplica_passo p pt) c'
  end.

(* Ponto final: destino a partir da origem. *)
Definition ponto_final (c : caminho) : ponto := destino origem c.

(* Testes: ambos os caminhos chegam em (1,1). *)
Example destino_c_RU : ponto_final c_RU = (1, 1).
Proof. reflexivity. Qed.

Example destino_c_UR : ponto_final c_UR = (1, 1).
Proof. reflexivity. Qed.

(** Equivalência entre caminhos*)
(** ======================================================================== *)

(* Dois caminhos são equivalentes quando um é permutação do outro. *)
Definition equiv (c d : caminho) : Prop := Permutation c d.

(* Caso emblemático: R;U equivale a U;R (regra perm_swap). *)
Example comuta_RU : equiv [Right; Up] [Up; Right].
Proof. unfold equiv. apply perm_swap. Qed.

(** Comutação de passos*)
(* ========================================================================= *)

(* A ordem de dois passos não altera o ponto alcançado. *)
Lemma aplica_passo_comuta : forall (p q : passo) (pt : ponto),
  aplica_passo p (aplica_passo q pt) = aplica_passo q (aplica_passo p pt).
Proof.
  intros p q pt.
  destruct p; destruct q; destruct pt as [x y]; simpl; reflexivity.
Qed.

(** Caminhos equivalentes têm o mesmo comprimento*)
(* ========================================================================= *)

(* Indução na derivação de Permutation (um caso por regra). *)
Lemma equiv_mesmo_comprimento : forall c d : caminho,
  equiv c d -> length c = length d.
Proof.
  intros c d H. unfold equiv in H.
  induction H.
  - (* perm_nil *) reflexivity.
  - (* perm_skip *) simpl. rewrite IHPermutation. reflexivity.
  - (* perm_swap *) simpl. reflexivity.
  - (* perm_trans *) rewrite IHPermutation1. exact IHPermutation2.
Qed.

(** Caminhos equivalentes têm o mesmo ponto final *)
(* ========================================================================= *)

(* Indução em Permutation, generalizando o ponto de partida pt. *)
Lemma equiv_mesmo_destino : forall c d : caminho,
  equiv c d -> forall pt : ponto, destino pt c = destino pt d.
Proof.
  intros c d H. unfold equiv in H.
  induction H; intros pt.
  - (* perm_nil *) reflexivity.
  - (* perm_skip *) simpl. apply IHPermutation.
  - (* perm_swap *) simpl. rewrite aplica_passo_comuta. reflexivity.
  - (* perm_trans *) rewrite IHPermutation1. apply IHPermutation2.
Qed.

(** Prova principal*)
(* ========================================================================= *)

(* Caminhos equivalentes têm mesmo comprimento e mesmo ponto final. *)
Theorem equiv_preserva : forall c d : caminho,
  equiv c d ->
  length c = length d /\ (forall pt : ponto, destino pt c = destino pt d).
Proof.
  intros c d H. split.
  - apply equiv_mesmo_comprimento. exact H.
  - apply equiv_mesmo_destino. exact H.
Qed.

(* A partir da origem, caminhos equivalentes terminam no mesmo ponto. *)
Corollary equiv_mesmo_ponto_final : forall c d : caminho,
  equiv c d -> ponto_final c = ponto_final d.
Proof.
  intros c d H. unfold ponto_final.
  apply equiv_mesmo_destino. exact H.
Qed.

(* Aplicação concreta: R;U e U;R terminam no mesmo ponto. *)
Example exemplo_comuta_ponto_final :
  ponto_final [Right; Up] = ponto_final [Up; Right].
Proof. apply equiv_mesmo_ponto_final. apply comuta_RU. Qed.
