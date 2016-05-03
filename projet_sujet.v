

(** *** Projet Coq 2016 - L3 S2 - Lucca Hirschi *)


(** Vous pouvez lire ce document dans sa version HTML mais l'idéal est de le compiler
au fur et à mesure pour lire les messages renvoyés par Coq.
 *)
(** Lien vers la page du projet:
<<http://www.lsv.ens-cachan.fr/~hirschi/enseignements/progLogique/
>>
 *)

(************************)
(** * I : Introduction **)
(************************)
(** Ce projet est constitué de trois parties pratiquement indépendantes. La première
section est assez facile conceptuellement mais demande d'écrire pas mal de preuves.
La seconde section demande plus de réflexion. Essayez de l'aborder en TP pour que
je puisse vous aider. La troisième section demande d'avoir lu la seconde.*)

(** Plan:
[II: Axiomes de la logique classique] Preuves autour de la logique classique et de ses axiomatisations
[III: Relations bien fondées] Deux notions de bonne fondaison pour les relations et relations entre
      ces définitions.
[IV: Récursions et relations bien fondées] Spécification faible vs. forte puis deux approches pour
     définir et spécifier des fonctions récursives non structurellement décroissantes.
 *)

(********************************************)
(** * II : Axiomes de la logique classique **)
(********************************************)
(** L'axiomatisation de base de Coq ne permet que de prouver des preuves en logique
intuitioniste (et non classique). Si l'on veut travailler dans une logique classique,
on doit alors déclarer un "axiome classique" dans Coq. On peut ajouter le raisonnement
par l'absurde, ou ajouter la loi de Peirce par exemple. L'objectif de la première partie
du projet est de montrer que les logiques classiques induites par cinq axiomes différents
ont la même expressivité.*)

Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~ P -> P.
Definition excluded_middle := forall P:Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).

(** *** Exercice 1: preuves classiques *)
(***************************************)
(** **** Question 1:*)(** Prouvez que les logiques induites par ces propriétés ont la même 
expressivité. Le plus simple est de choisir un ordre (par exemple
classic => peirce => implies_to_or => ... => classic) et prouvez une série de lemmes de la forme:
                       *)

(* Abréviations : 
 * peirce : pl (peirce law)
 * classic : cl
 * excluded_middle : em
 * de_morgan_not_and_not : dm
 * implies_to_or : ito
 *)

(* Ordre choisi : 
 * classic => peirce => excluded_middle => implies_to_or 
 * => de_morgan_not_and_not => classic
 *)

(* Pour montrer les lemmes, on va se contenter de montrer des lemmes du type loi1 => loi2. Pour cela, on a besoin du lemme intermédiaire suivant : *)

Lemma simple_to_complex : forall A B:Prop, (B->A) -> (forall P : Prop, (A->P) -> (B->P)).
Proof.
intros A B BiA P AiP Bt.
apply AiP.
apply BiA.
assumption.
Qed.



(***** Classic => peirce *****)
Lemma cl_pl : forall P:Prop, (classic -> P) -> (peirce -> P).
apply simple_to_complex.
intro pl.
intros P nnP.
assert ((~P -> P) ->P) as plPFalse. (*on applique pl avec P et false*)
apply pl.
apply plPFalse.
intro nP.
destruct nnP.
assumption.
Qed.



(***** Peirce => excluded_middle *****)
Lemma pl_em :  forall P:Prop, (peirce -> P) -> (excluded_middle -> P).
Proof.
apply simple_to_complex.
intro em.
intros P Q.
assert (P\/~P) as emP.
apply em.
destruct emP as [Ptrue|nP].

intro . (*si P*)
assumption.

intro imp. (*si ~P*)
apply imp.
intro Ptrue.
destruct nP.
assumption.
Qed.


(***** excluded_middle => implies_to_or *****)

(*Question : ici, le ; ne permet pas de factoriser le code... Comment faire.*)
Lemma or_commut : forall P Q:Prop, P\/Q <-> Q\/P.
Proof.
intros P Q.
split.
intro or.
destruct or.
right.
assumption.
left.
assumption.
intro or.
destruct or.
right.
assumption.
left.
assumption.
Qed.

Lemma em_ito :  forall P:Prop, (excluded_middle -> P) -> (implies_to_or -> P).
Proof.
apply simple_to_complex.
intro ito.
intro P.
assert ((P->P)->~P\/P) as itoPP.
apply ito.
apply or_commut.
apply itoPP.
intro Pt.
assumption.
Qed.



(***** implies_to_or => de_morgan_not_and_not *****)
Lemma ito_dm : forall P:Prop, (implies_to_or -> P) -> (de_morgan_not_and_not -> P).
Proof.
apply simple_to_complex.
intros dm P Q PiQ.
assert (~(~~P/\~Q) -> (~P \/ Q)) as dm_nPQ. (*on applique dm avec ~P et Q*)
apply dm.
apply dm_nPQ.
intro nAnd.
destruct nAnd as [nnP nQ].
destruct nnP.
intro Ptrue.
destruct nQ.
apply PiQ.
assumption.
Qed.




(***** de_morgan_not_and_not => classic *****)
Lemma dm_cl :  forall P:Prop, (de_morgan_not_and_not -> P) -> (classic -> P).
Proof.
apply simple_to_complex.
intros cl P Q nAnd.
apply cl.
intro nOr.
destruct nAnd.
split.

intro nP. (*on montre ~P ... *)
destruct nOr.
left.
assumption.

intro nP. (*puis ~Q*)
destruct nOr.
right.
assumption.
Qed.


(** **** Question 2:*)(** Prouvez la dualité classique entre [exists] et [forall].*)
Theorem forallExists : forall A, forall P : A -> Prop,
                         peirce -> (~ (forall x : A, P x) <-> (exists x : A, ~ P x)).
Proof.
intros A P.
apply cl_pl.
intro cl.
split.

intro nforall. (* => *)
apply cl.
intro nexists.
destruct nforall.
intro x.
apply cl.
intro nPx.
destruct nexists.
exists x.
assumption.

intro exists_nPx. (* <= *)
destruct exists_nPx as [x nPx].
intro forallPx.
destruct nPx.
apply forallPx.
Qed.


(** Et le symétrique? A-t-on besoin de la logique classique? *)

(*ici, on n'a pas besoin de la logique classique car on n'utilise à aucun moment un lemme équivalent au tiers exclus*)
Theorem existsForall : forall A, forall P : A -> Prop,
                         (~ (exists x : A, P x) <-> (forall x : A, ~ P x)).
Proof.
intros A P.
split.

intros nexists x nPx. (* => *)
destruct nexists.
exists x.
assumption.

intros forallnPx existsPx. (* <= *)
destruct existsPx as [x Px].
assert (~P x) as nPx.
apply forallnPx .
apply nPx.
assumption.
Qed.


(**************************************)
(** * III : Relations bien fondées   **)
(**************************************)
(** Il faut avoir lu la seconde section pour aborder celle-ci. *)
(** Dans cette section, on va formaliser le prédicat "relation bien fondée" et on va prouver,
entre autre, l'implication et la réciproque entre:
 - (i) une relation est bien fondée (selon notre formalisation),
 - (ii) une relation n'admet pas de suite infinie décroissante.*)
(** Le sens direct est prouvable en logique intuitionniste. On introduira donc
pas d'axiome supplémentaire. On prouvera par contre la réciproque en logique classique (avec l'un
des axiomes de la section II) + un axiome magique.*)


(** ** 1. Sens direct en logique intuitionniste **)
(*************************************************)
(** Il faut commencer par formaliser cette propriété (i) en Coq. Commençons par les relations.
On se limitera dans ce projet aux relations entre un même ensemble. Le type des relations sur un
ensemble A s'écrit donc [R : A -> A -> Prop]. Regardez par exemple la relation "<" sur les
entiers:*)
Check (lt: nat -> nat -> Prop).
(** Pour formaliser qu'une relation est bien fondée (i) on va définir un prédicat [Acce] sur les
 éléments [x] d'un ensemble [A]:
(a) les éléments minimaux pour [R] vérifient le prédicat,
(b) si tous les éléments [y] plus petits que [x] vérifient le prédicat alors [x] le vérifie aussi.
On note que (a) est un cas particulier de (b) ce qui nous permet d'écrire: *)
Inductive Acce (A:Set) (R:A->A->Prop) : A->Prop :=
  Accessible : forall x:A, (forall y:A, R y x -> Acce A R y) -> Acce A R x.
(** Intuitivement, [Acce A R x] est prouvable si vous avez une preuve (et donc un objet fini)
qui explore tous les éléments plus petits que [x]. Moralement, ce prédicat est donc prouvable
uniquement pour les éléments qui n'appartiennent à aucune chaîne infinie décroissante.*)

(** On peut donc formaliser le prédicat "bien fondée":*)
Definition bienFonde (A:Set) (R:A->A->Prop) : Prop := forall a:A, Acce A R a.
(** Cette présentation est plus effective que (ii), si vous prouvez qu'une relation
est bienFondé alors vous construisez une fonction qui pour tout élément de [A]
explore toutes les chaînes descendantes à partir de cet élément. C'est un outil
essentiel pour pouvoir définir des fonctions récursives bien fondées mais non
structurellement décroissantes comme nous le verrons dans la partie IV. *)

(** Remarquez qu'on a (pratiquement) redéfinit  des termes existants : *)
Print Acce.
Print well_founded.


(** *** Exercice 2: Préliminaires **)
(***********************************)
(** **** Question 1:*)(** Ecrivez le prédicat sur les relations vérifiant (ii):
"la relation n'admet pas de suite infinie décroissante". Ecrivez l'énoncé du sens direct).*)
(**  *)

(*
Definition infDec (A:Set) (R:A->A->Prop) : Prop := exists a:A, forall b:A, R b a /\ a <> b -> exists c:A, R c b /\ b <> c.

Check infDec.
Definition notInfDec(A:Set) (R:A->A->Prop) : Prop := forall a:A, exists b:A, forall c:A, R b a /\ a<>b /\ (R c b -> b = c). (*(~R c b \/ b = c). *)
*)

(* ici une suite est une fonction de N dans un certain ensemble A*) 
Definition bienFonde2 (A:Set) (R:A->A->Prop) : Prop := 
  ~ (exists seq : nat->A, forall n : nat, R (seq (S n)) (seq n)).



(*Theorem direct : forall A:Set, forall R:A->A->Prop, bienFonde A R -> notInfDec A R.
Proof.
admit.
Qed.*)

(** **** Question 2:*)(** Pour vous échauffer, prouver les deux lemmes suivants qui pourront
vous servir dans la suite.*)

Lemma acce_uneEtape : forall (A:Set) (R : A -> A -> Prop) (a b:A),
                        R a b -> Acce A R b -> Acce A R a.
intros A R a b aInfb bAcce.
inversion bAcce.
apply H.
assumption.
Qed.

Lemma nonAcce_uneEtape : forall (A:Set) (R : A -> A -> Prop) (a b:A),
                           R a b -> ~ Acce A R a -> ~ Acce A R b.
intros A R a b aInfb aNotAcce bAcce.
destruct aNotAcce.
apply acce_uneEtape with (b:=b);assumption.
Qed.


(**  *)   
(** **** Question 3:*)(** Prouvez maintenant le lemme suivant permettant de réaliser des inductions
en exploitant une relation bien fondée (notez que c'est le but premier des relations bien
fondées: permettre d'aller au delà des fonctions récursives structurellement décroissantes).
Lui aussi pourra vous être utile. Pensez bien au lemme d'induction généré par la définition
inductive du prédicat [Acce].*)

Lemma bienFonde_ind : forall (A : Set) (R : A -> A -> Prop),
                        bienFonde A R ->
                        forall P : A -> Prop,
                          (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
                          forall a : A, P a.

Check Acce_ind.
intros A R bfR P heredite a.
apply Acce_ind with (A:=A) (R:=R).
unfold bienFonde in bfR.
intros x RimpAcce RimpP.
apply heredite.
assumption.
unfold bienFonde in bfR.
apply bfR.
Qed.

(**  *) 
(** *** Exercice 3: Preuves de bonne fondaison **)
(************************************************)
(** **** Question 1:*)(** On montre que la relation [< : nat -> nat -> Prop] est bien fondée 
(conseil: vous aurez besoin d'un lemme d'induction forte).*)
Check nat_ind.

Lemma strong_induction : forall P : nat -> Prop, P 0 -> (forall m : nat, (forall n : nat, lt n m -> P n) -> P m) -> forall k : nat, P k.
intros P P0 heredite n.
apply heredite.
induction n.

intros n2 n2lt0. (*initialisation*)
unfold lt in n2lt0.
inversion n2lt0.

intros n0 n0ltSn. (*hérédité*)
inversion n0ltSn.
apply heredite.
assumption.
apply IHn.
assumption.
Qed.

Lemma lt_bienFonde : bienFonde nat lt.
unfold bienFonde.
apply strong_induction.

apply Accessible. (*initialisation*)
intros y ylt0.
inversion ylt0.
intros m H. (*hérédité*)
apply Accessible.
assumption.
Qed.



(** **** Question 2:*)(** Ecrivez le prédicat [lex] qui prend deux relations et qui formalise
la relation lexicographique sur ces deux relations. Prouvez maintenant que si deux relations
sont bien fondées alors la relation lexicographique de ces deux relations l'est aussi.*)
(**  *)     
Print le.
Locate "(".
Print pair.
Print prod.
Print nat.
Print S.

Inductive lex (A:Set) (R:A->A->Prop) (R' : A->A->Prop) : A*A -> A*A -> Prop := 
fstInf : forall c c' : A*A, R (fst c) (fst c') -> lex A R R' c c'
|sndInf :  forall c c' : A*A, fst c = fst c' /\ R' (snd c) (snd c') -> lex A R R' c c'.

Lemma bfLex : forall (A:Set) (R R':A->A->Prop), bienFonde A R -> bienFonde A R' ->bienFonde (A*A) (lex A R R').
Proof.
(*intros A R R' bfR bfR'.
unfold bienFonde.
intro a.
apply Accessible.
intros y ylexa.
unfold lex in ylexa.
destruct ylexa.
unfold bienFonde in bfR.*)
admit.
Qed.

Check bienFonde_ind.
(** *** Exercice 4: Le sens direct **)
(************************************)
(** Et maintenant, prouvez le sens direct de l'équivalence entre (i) et (ii). *)
(**  *)     
Theorem direct : forall A:Set, forall R:A->A->Prop, bienFonde A R -> bienFonde2 A R.
Proof.
unfold bienFonde2.
intros A R bfR existsInfDec.
destruct existsInfDec as [seq seqIsInfDec] .

assert (forall a:A, (exists n : nat, a = seq n) -> ~ Acce A R a).
intro a.
apply bienFonde_ind with (R:=R).
assumption.
intros x HI aSeqn.
apply HI with (y:=a).
Qed.


(** ** 2. Réciproque en logique classique **)
(*******************************************)
(** On s'attaque maintenant à la réciproque!*)

(** *** Exercice 5: Préliminaires **)
(***********************************)
(** La réciproque n'est pas prouvable en logique intuitionniste (des intuitions? écrivez-les).
On introduit donc un axiome classique que l'on pourra utiliser dans la suite. La syntaxe est
"[Axiom [nom_axiome] : P.]".*)

(** Tentez de prouver la réciproque sur papier en logique classique.
 De quoi avez-vous besoin ?
 Est-ce que c'est prouvable dans Coq (avec l'axiome classique) ?*)
(** Vous avez le droit d'ajouter un axiome tant qu'il appartient à la
théorie des ensembles de Zermelo-Fraenkel
(cf.Wikipedia).*)
(**  *)

(** *** Exercice 6: la réciproque **)
(***********************************)
(** Et maintenant, muni de ces deux axiomes, prouvez la réciproque.*)


(**************************************************)
(** * IV : Récursions et relations bien fondées  **)
(**************************************************)
(** On revient maintenant sur les fonctions récursives totales mais non structurellement décroissantes
(comme la  fonction pgcd vue en TP). Nous allons voir que les relations bien fondées font parties
des ingrédients nécessaires dans les deux approches discutées dans les deux sous-sections suivantes.
L'objectif est ici d'écrire une fonction pgcd et de prouver sa spécification (i.e., elle calcule
bien le pgcd). *)
(** Dans cette section on s'autorise l'aide de la tactique [omega] qui résout pas mal de systèmes
d'équations et d'inéquations de [nat]. *)
Require Import Omega.

(** Avant de commencer, il nous faut comprendre les notions de spécification faible vs. sépcification
forte. Prenons par exemple, un prédicat [R: A -> B -> Prop] représentant une spécification d'une
fonction [f : A -> B]. On dit que [f] vérifie la spécification [R] quand [forall a:A, R a (f a)].
- (i) Une spécification faible consiste à définir la fonction [f:A->B] dans un premier temps puis
à prouver dans un second temps qu'elle vérifie sa spécification attendue.
- (ii) Une spécification forte consiste à écrire la spécification de [f] dans son type. Typiquement,
un tel type combinera des informations sur les types des données manipulées et des propositions
qu'ils doivent vérifier. Par exemple une spécification forte de la division euclidienne pourrait être
le type suivant: *)
Variable euclideType :forall a b:nat, 0 < b ->
                                      {p:nat*nat | a = (fst p)*b + snd p /\ 0 <= snd p < b}.
(** Ce type décrit les fonctions qui prennent deux entiers [a] et [b], une preuve que [0<b]
et renvoie une paire d'entiers [p] décrivant (couple,quotient) avec les propriétés attendues. *)
(** Formellement, voici comment est défini [{x:A | P }]: *)
Print sig.
(** On voit bien que ce type décrit les éléments de [A] embarquant une preuve qu'ils vérifient [P]. *)
(** Un habitant du type [{x:A | P}] n’est pas tout à fait un habitant du type [A]. Cependant, on
peut toujours le décomposer pour en extraire un élément de type [A] qui satisfait la propriété [P],
à l’aide de la construction match. Voici un exemple: *)
Definition removeSpec (a : {x : nat | x > 0}) : nat  :=
  match a with
    | exist a' Pa => a'
  end.
Check removeSpec.
(** Voyons maintenant comment composer des spécifications. Par exemple: *)
Check le_gt_dec.
Check (le_gt_dec 1 2).
(** Le "+" de [le_gt_dec] est l'équivalent du ou logique mais à valeur dans les données (possiblement
spécifiées). *)
Print sumbool.
Print le_gt_dec.

(** *** Exercice 7: Spécifications et types dépendants *)
(*******************************************************)
(** Question 1: En utilisant les fonctions [div2_of_even] et [test_even], écrivez une fonction dont
 le type est [forall n : nat, {p:nat | n = p+p}+{p:nat | pred n = p+p}]. *)
Require Import Coq.Arith.Even.
Open Scope nat_scope.
Parameter div2_of_even : forall n:nat, even n -> {p:nat | n = p+p}.
Parameter test_even : forall n:nat, {even n}+{even (pred n)}.

(** Question 2: Ecrivez (sans tactique) une fonction prédecesseur fortement spécifiée. *)


(** Question 3: Ecrivez (uniquement avec des tactiques) une fonction prédecesseur fortement spécifiée. *)
Reset pred'.
Definition pred' : forall n:nat, {p:nat | n = S p}+{n = 0}.
  (** Vos tactiques ici ... *)
Defined.



(** *** Exercice 8: Définitions par équation et par induction bien fondée *)
(**************************************************************************)

(** ** 1. Définition par équation **)
(***********************************)

(** L'idée de cette approche est de raisonner en trois temps:
a. écrire le corps de la fonction
b. démontrer sa terminaison
c. construire le point fixe et prouver sa spécification
 *)

(** a. L'idée est de remplacer une définition inductive [f x = expr] où [expr] contient [f] par
une équation de point fixe [f x = F f x] (f étant le point fixe de [F]). Par exemple voici le [F]
que l'on pourrait définir dans le but de calculer la division euclidienne. *)
Definition div_it_F (f:nat->nat->nat*nat) (m n:nat) :=
  match le_gt_dec n m with
    | left _ => let (q, r) := f (m-n) n in (S q, r)
    | right _ => (0, m)
  end.
(** On définit maintenant la fonction qui itère [F] un certain nombres de fois: [F^n g a] *)
Fixpoint iter (A:Set) (n:nat)(F:A->A)(g:A){struct n} : A :=
  match n with
      O => g
    | S p => F (iter A p F g)
  end.
Implicit Arguments iter [A].

(** b. On peut maintenant montrer la terminaison: pour des entiers [n,m] il va toujours exister un
nombre d'itération [p] pour lequel on atteint le point fixe de [F]. *)
Definition div_it_terminates :
  forall n m:nat, 0 < m ->
                  {v : nat * nat |
                   exists p : nat, (forall k:nat, p < k -> forall g:nat -> nat -> nat * nat,
                                                             iter k div_it_F g n m = v)}.
  intro n.
  (** On veut faire une induction forte sur [n]: *)
  elim n using (well_founded_induction lt_wf).
  (** Question 1: Terminez la preuve *)
Defined.

(** c. Construction du point fixe. *)
Definition div_it (n m:nat)(H:0 < m) : nat*nat :=
  let (v, _) := div_it_terminates n m H in v.
(** Preuve du point fixe *)
Theorem div_it_fix_eqn :
  forall (n m:nat)(h:(0 < m)),
    div_it n m h =
    match le_gt_dec m n with
      | left H => let (q,r) := div_it (n-m) m h in (S q, r)
      | right H => (0, n)
    end.
Proof.
  (** Question 2: Ecrivez la preuve. *)
Qed.

(** Preuve de Correction *)
Theorem div_it_correct1 :
  forall (m n:nat)(h:0 < n),
    m = fst (div_it m n h) * n + snd (div_it m n h).
Proof.
  intros m; elim m using (well_founded_ind lt_wf).
  (** Question 3: Terminez la preuve. *)
Qed.
Theorem div_it_correct2 :
  forall (m n:nat)(h:0 < n), snd (div_it m n h) < n.
Proof.
  (** Question 4: Ecrivez la preuve. *)
Qed.



(** ** 2. Définition par induction bien fondée **)
(************************************************)

(** L'approche précédente utilisait une spécification faible des fonctions manipulées. Dans cette
section, on va voir comment définir des fonctions récursives en incorporant leur bonne fondaison
dans leur type. On en profitera pour donner des spécifications fortes. *)
(** Le principal outil que l'on utilisera est la fonction [well_founded_induction]. *)

Require Import Wellfounded.


Check well_founded_induction.
(** Cette fonction prend 5 arguments et renvoie une fonction de type [∀ x:A, P x]. Décrivons ses
arguments:
  1. [A] (de type [Set]) est le domaine de la fonction que l'on est en train de définir
  2. [R:A->A->Prop] est une relation binaire sur [A]
  3. [well_founded A R] est une preuve que [R] est bien fondée
  4. [P:A->Set] est une fonction qui calcule le type de la fonction que l'on est en train de calculer      (elle associe à chaque input un type de retour dans [Set] qui contiendra sa spécification)
  5  [(∀ x:A, (∀ y:A, R y x -> P y) -> P x)] est une fonction qui prend en argument:
       (a) un argument [x:A],
       (b) une fonction qui en fonction d'un élement [y:A] et d'une preuve que [y] "est plus petit"
           que [x] renvoie le résultat attendu pour [x]
     et qui renvoie le résultat attendu pour [x]. On voit que cette fonction nous calcule le résultat
     pour [x] en fonction des résultats pour les [y] plus petits que [x]. En quelque sorte, son type
     la contraint à ne faire que des appels récursifs bien fondés vis à vis de [R].
Au final, [well_founded_induction] nous construit en sortie un terme de type [∀ x:A, P x] c'est à dire
une fonction qui à [x:A] nous donne un élément de [P x] vérifiant la spécfication.
 **)
(** Voyons comment utiliser cette fonction dans le cas d'une fonction calculant la division
    euclidienne.
1. nat
2. relation lt *)
Print lt.
(** 3. lt_wf (équivalent de lt_bienFonde prouvée dans la partie III) *)
Print lt_wf.
(** 4. définition suivante: *)
Definition div_type (m:nat) := forall n:nat, 0 < n -> {q:nat & {r:nat | m = q*n+r /\ r < n}}.
(** 5. La fonction doit avoir le type [∀ x:nat, (∀ y:nat, y < x → div_type y)→ div_type x]. Nous
allons la construire avec des tactiques. *)
Definition body_div :
  forall x:nat, (forall y:nat, y < x -> div_type y) -> div_type x.
  intros m rec.
  unfold div_type.  
  intros n G.
  destruct (le_gt_dec n m).
  (** Question 5: Terminez la définition. *)
Qed.
(** Pour garder plus de contrôle sur la fonction que l'on est en train de définir, il est possible
    d'utiliser la tactique [refine <terme>] pour un terme contenant des [_]. La tactique va essayer
    de matcher le terme avec le type et décharger une partie des preuves qu'elle n'arrive pas
    à trouver. Exemple: *)
Definition Body_div' :
  forall x:nat, (forall y:nat, y < x -> div_type y) -> div_type x.
  unfold div_type at 2.
  (**
  refine (fun m div_rec n Hlt =>
            match le_gt_dec n m with
              | left H_n_le_m =>
                match div_rec (m-n) _ n _ with
                  (** Notez la présence des [_]: Coq vous demandera ensuite de donner des termes
                        pour remplir les trous ce qui correspond à prouver les spécifications des
                        arguments de [dic_rec]. *)
                  (** TODO **)
                  | right H_n_gt_m =>
                    (** TODO **)
                end).
   *)
  admit.
Defined.


(** On peut maintenant écrire notre fonction comme décrit plus haut: *)
Definition div :
  forall m n:nat, 0 < n -> {q:nat &{r:nat | m = q*n+r /\ r < n}} :=
  well_founded_induction lt_bienFonde div_type body_div.
Print div.
(** Aucun lemme de correction n'est nécessaire car [div] est fortement sépcifiée ;) *)



(** ** 3. PGCD *)
(***************)

(** *** Exercice 9: preuve de PGCD **)
(**************************************)
(** choisissez l'approche de votre choix pour écrire et prouver une fonction calculant le PGCD de deux entiers. *)