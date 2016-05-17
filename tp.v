(** *** Projet Coq 2014 - L3 S1 - Lucca Hirschi *)


(** Vous pouvez lire ce document dans sa version HTML mais l'idéal est de le compiler
au fur et à mesure pour lire les messages renvoyés par Coq.
Vous avez besoin de Coq et d'un front-end (par exemple
CoqIDE par défaut dans Coq ou Proof General pour l'interface avec Emacs).
Ce TP vous expliquera les notions essentielles de l'outil Coq. Il contient peu de questions
mais beaucoup d'explications. Assurez-vous donc de bien comprendre au fur et à mesure.
 *)
(** Lien vers la page du projet:
<<http://www.lsv.ens-cachan.fr/~hirschi/enseignements/progLogique/
>>
 *)

(************************)
(** * I : Introduction **)
(************************)

(** ** 1. Généralités **)
(***********************)
(** Une des contributions de l'informatique à la logique sont les outils construisant
des preuves. Il existe deux catégories principales de ces outils:
 - les prouveurs automatiques tels que les SAT ou SMT solveurs ainsi que les model checkers, etc. 
   Vous en avez donc déja utilisé un lors du premier mini projet;
 - les assisants de preuves tels que Coq, Abella, PVS ou Agda, etc. Ce sont des outils interactifs
   construisant des preuves en demandent une intervention humaine mais qui automatisent certaines tâches.

Dans ce projet on utilisera Coq (dans la seconde catégorie). En quelques mots, Coq est composé:
- d'un "proof-checker" qui vérifie que la preuve construite est bien une suite de règles logiques correctement utilisées. C'est le (petit) noyau dans lequel il faut avoir confiance,
- d'un langage fonctionnel permettant de programmer et de formaliser des théories, calculs, etc.,
- et d'un langage de "tactiques" permettant d'automatiser certaines étapes de preuves.
Le noyau de Coq repose sur de solides fondations: le calcul des constructions.
 *)

(** ** 2. Démarrer Coq **)
(************************)
(** Je vous conseille d'utiliser l'une des deux solutions suivantes:
 - l'IDE fourni avec COQ. Vous le lancez en tapant 'coqide' dans un terminal ou
 - le mode Emacs Proof General que vous pouvez trouver ici: 'http://proofgeneral.inf.ed.ac.uk/'.

Mais allez au plus simple pour pouvoir continuer à lire le sujet (dans Coq).
 *)

(** ** 3. Les types de Coq **)
(****************************)
(** Dans le langage de Coq (aka Gallina) vous pouvez écrire des formules, vérifier
qu'elles sont correctement formées et les prouver.*)
(** En Coq, tous les objets sont des termes du langage et ont donc un type que vous
    pouvez afficher avec la commande [Check [terme].] (toute commande Coq doit se
    terminer par un ".").*)
Check 3.
Check nat.
Check Set.
Check Type.
(** La notation [A:B] indique que le terme [A] a le type [B].
    On verra que de façon équivalente, ça signifie également que [A] est une preuve
    de [B].*)
Check 1=2.
Check True.
Check (forall x:nat, x=0 \/ x>0).
Check Prop.
(** Bien-sûr, certains termes sont mal formés comme [1+True] par exemple (essayez de compiler puis
commentez la ligne suivante): *)
 (*Check (1 + True).*)

(** Une bonne façon de s'y retrouver dans tous ces types est d'avoir en tête que:
     - les termes de type [Prop] correspondent aux propositions logiques (ex. [1=2] ou [True]),
     - les termes de type [Set] sont des types de données (ex. nat),
     - les termes de type [T] où [T] est un type de donnée (i.e., [T:Set]) sont des données (ex. 1),
     - et.... [Type] est tout en haut (on a [Prop:Type] et [Set:Type]).
Avec un schéma ça donne (une arrête signifie 'est de type'):
<<
                 Type
               /      \
            Set       Prop
           /  |      /    \
        nat  bool  True  ((1=0) \/ False)
       / |   /  \
      1  0  true false
>> *)
(** Dans la suite, on va rapidement voir la syntaxe de ce langage, à savoir comment écrire
des fonctions et des propositions et comment les prouver. On commence dans la section
suivante (II) avec les définitions de fonctions et de données (on restera dans le monde [Set]).
Puis dans la section III sur les preuves, on plongera dans le monde [Prop].*)      



(******************************)
(** * II : Programmer en Coq **)
(******************************)

(** ** 1. Fonctions, calcul, bool *)
(** La commande [Require Import [module]] permet de charger les définitions, lemmes,
théorèmes et leurs preuves d'un module. *)
Require Import Bool.
(** Je peux maintenant chercher toutes les définitons du module. *)
Search bool.
(** Je peux afficher la définition d'un terme avec [Print].*)
Print bool.
(** [bool] (qui est lui même de type [Set]) est un type de donnée contenant deux éléments [true] et [false].
      On dit aussi que les habitants de [bool] sont [true] et [false].
      Quelle est la différence avec [True:Prop]? *) 
Print ifb.
(** On peut donc écrire une fonction avec le mot clé [fun] jouant le rôle d'un lambda: *)
Check (fun (b:bool) (n:nat) => if b then n else 0).
(** On note la distinction entre la flèche [=>] des fonctions et celle des types: [->].
Si on veut définir un terme ou une fonction (pour l'utiliser par la suite), on utilise
le mot clé [Definition]. L'exemple suivant comprend pas mal de points de syntaxe:*) 
Definition ifb2 (b : bool) (n:nat) := 
  let ntrue := n-1 in
  let nfalse := n in
  match b with
    | true => ntrue
    | false => nfalse
  end.
(** On peut aussi écrire: *)
Definition f := fun b:bool => b.
(** qui est équivalent à: *)
Definition f2 (b:bool) := b.  
Print f.
Print f2.
(** On essaye d'appeler notre fonction: *)
Check (ifb2 true 1).
(** Et oui, Coq ne réduit pas le terme qu'on lui donne, il vérifie juste son type.
    Si on veut réduire le terme, alors il faut invoquer [Eval compute in [terme]]
    et Coq va effectuer le calcul (purement symbolique!).*)
Eval compute in (ifb2 true 1).
(** En Coq, toute fonction est TOTALE. C'est-à-dire que les fonctions
    terminent TOUJOURS et renvoient un résultat du bon type. Il n'y a pas d'exceptions,
    d'erreurs à runtime ou d'Obj.magic.*)

(** **** Question 1:*)(** Ecrivez une fonction qui renvoie le XOR de trois booléens et testez-la. *)

Definition XOR (b1 b2 b3:bool) := 
xorb (xorb b1 b2) b3.

Print XOR.

Eval compute in (XOR true false false).
(** ** 2. Définitions inductives, points fixes et nat **)
(*******************************************************)
Print nat.
(** Les entiers sont représentés comme des entiers de Peano: c'est l'axiomatisation
    de Peano. Si vous voulez invoquer des propriétés sur les entiers qui ne sont pas des lemmes déjà
    écrits (dans le module [Arith] par exemple) alors il faut les prouver dans Coq.*)
(** On note le mot clé [Inductive] qui permet de définir:
      - un type de données lui-même de type [Set] (ici c'est [nat]),
      - ainsi que les habitants de ce type (les termes qui ont ce type). Ici il n'y a que le
        terme 0 qui est un entier et le terme "S" (successeur) qui a le type [nat -> nat].
      C'est l'équivalent d'une définition inductive par fermeture de règles (ou fonctions constructeurs)
      vue en logique. Dans le cas de [nat], on définit un ensemble inductif [nat] de termes par fermeture
      des fonctions constucteurs suivantes:
<<
                                      n : nat
     ----------------- [0]       --------------- [Succ]
          0 : nat                  S(n) : nat
        
>>
 *)
Search nat.
Print pred.
(** Ok, rien de nouveau. Maintenant, comment écrire [plus] ? Pensez-y avant d'avancer. *)
Print plus.
(** [fix] est un raccourci pour le mot clé [Fixpoint] qui permet de définir des fonctions
récursives (un peu comme le "let rec" d'Ocaml).*)
Fixpoint mon_mult (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + mon_mult p m
  end.

Check mon_mult.
(** Notez bien le message renvoyé par Coq après la définition de fonction:
[mon_mult is recursively defined (decreasing on 1st argument)]. Coq détecte que
l'induction est bien fondée. C'est de cette façon qu'il s'assure que toutes les fonctions
terminent. Le critère (syntaxique) de Coq est le suivant: un argument au moins DOIT être structurellement
plus petit au moment de l'appel récursif qu'à l'entrée de la fonction. Regardez-les deux
exemples suivants.*)
(*Fixpoint fail1 (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + fail1 (S p) m
  (* et oui ça boucle ici *)
  end.*)
(*Fixpoint fail2 (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + fail2 (p + 0) m
  (** et oui c'est plus petit mais pas structurellement plus petit *)
  end.*)

(** **** Question 2:*)(** Ecrivez une fonction qui prend un entier et qui renvoie [true]
s'il est pair et [false] sinon. Exécutez cette fonction sur plusieurs exemples.  *)
Search bool.
Fixpoint pair (n:nat) := 
  match n with
    | 0 => true
    | S p => negb (pair p)
  end.

Eval compute in pair 4.
Eval compute in pair 11.

(** **** Question 3:*)(** Ecrivez un type de données [arbre] contenant une représentation
de tous les arbres binaires étiquetés par des entiers.  *)
Search nat.
Inductive arbre : Set := F : nat -> arbre | N : nat -> arbre -> arbre -> arbre.

(** **** Question 4:*)(** Ecrivez une fonction qui renvoie la somme de toutes les étiquettes
des noeuds d'un arbre. Testez.  *)

Fixpoint somme_arbre (a:arbre) := 
  match a with 
     | F n => n
     | N p a1 a2 => p + somme_arbre a1 + somme_arbre a2
   end.

Eval compute in somme_arbre (N 4 (F 5) (F 7)).
(** **** Question 5:*)(** Ecrivez une fonction qui prend deux entiers et qui renvoie
[true] si le premier est plus petit que le second et [false] sinon. Testez.  *)

Fixpoint cmp (n m : nat) := 
  match (n,m) with 
    |(0,_) => true
    |(_,0) => false
    |(S p, S q) => cmp p q
  end.

Eval compute in cmp 4 3.
Eval compute in cmp 4 4.
Eval compute in cmp 3 4.
(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Ecrivez une fonction qui calcule le pgcd de deux entiers. Testez.  *)
Search nat.

Fixpoint reste' (n m p : nat) := 
  match (n,m,p) with
    |(_,0,_) => 0 (*ceci ne devrait pas se produire*)
    |(0,_,r) => r
    |(S n',S m',0) => reste' n' m m'
    |(S n',_,S p') => reste' n' m p'
   end.

Fixpoint reste (n m :nat) :=
  match reste' n m 0 with
    |0 => 0
    | k => minus m k
  end.

Eval compute in reste 4 2.

Fixpoint pgcd' (n m p:nat ) := 
   match n,m,p with
     | _,_,0 => 0 (* ceci ne doit pas arriver  sauf si n = m = 0*)
     | 0,_,_ => m
     | _,0,_ => n
     | _,_,S p' => 
     match reste n p , reste m p with
       | 0,0 => p
       | _,_ => pgcd' n m p'
     end
   end.



Fixpoint pgcd (n m :nat) := 
  if cmp n m then (*si n est le plus petit*)
    pgcd' n m n
  else
    pgcd' n m m.

Eval compute in pgcd 40 150.



(** ** 3. Types polymorphes, listes et types dépendants **) 
(*********************************************************)
Require Import List.
Check list. Print list.
(** Le type [list] est une fonction qui prend un type [A] et renvoie un type (le type des
listes de type [A]).*)
Check (list nat).
Check 1 :: 2 :: 3 :: nil.
(** Mais qu'est-ce que c'est que "::" ? (tout est un terme en Coq).*)
Locate "::".
(** [Locate] nous informe que "[::]" est juste un mot clé pour le terme [cons] (en notation infix).*)
(** Petit coup d'oeil rapide aux fonctions de [list].*)
Search list.  Check map. Print map.
Eval compute in map S (1::2::3::4::nil).
Eval compute in map (fun x => x +2) (1::2::3::4::nil).
Locate "++". Print app.

(** Très bien mais il n'existe pas de fonction pour accéder au n-ieme élément
    d'une liste, pourquoi? *)


(** Jusqu'ici on a vu:
   - des termes dépendant de termes (par exemple [S : nat -> nat]);
   - des types dépendant de types (par exemple [list : Type -> Type]).
   Il existe aussi des types dépendant de termes (aka types dépendants).
   Voici un exemple de type dépendant: un tableau de taille donnée:*)
Inductive array (n : nat) : Type :=
  tab : forall l : list nat, length l = n -> array n.
(** [array] est de type [nat -> Type]. Par exemple, [array 10] est le type des tableaux de
    taille 10. *)
Check array.
Check (array 10 : Type).
(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Ecrire une fonction qui réalise le fold_left polymorphique d'OCaml sur les listes.  *)
Search list.
Print map.

Fixpoint fold_left {A B:Set} (f : A->B->A) (a : A) (l : list B) := 
  match l with 
    | nil => a
    | h :: t => f (fold_left f a t) h 
  end.
Search nat.
Eval compute in fold_left plus 0 (1::32::2::3::4::nil).
(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Ecrire une fonction de tri.  *)
Locate Nat.


(* bon j'ai fait ça au dernier moment et la librairie nat ne voulait pas s'installer. Du coup, je suis pas sûr que ça marche*)
Fixpoint insert (n:nat) (l:list nat) :=
  match l with
    | nil => n::nil
    | h::t => if ltb h n then
                h::(insert n h)
              else
                n::h::t
    end.

(*ici, on va utiliser un tri par insertion basique*)
Fixpoint sort (l: list nat) :=
  match l with
    |nil => nil
    |h::t => insert h (sort t)
  end.
      

(** ** 4. Résumé **)
(******************)
(** Voici quelques lignes de Coq que vous devez comprendre (ainsi que les messages renvoyés Coq).*)
Check true. Check bool. Check Set.
Print bool.
Fixpoint mon_exp (n m : nat) : nat :=
  match m with
    | 0 => 1
    | S m' => n * mon_exp n m'
  end.
Eval compute in (mon_exp 2 5).
Inductive formula : Type :=
  MonTrue : formula
| MonFalse : formula
| MonEt : formula -> formula -> formula
| MonOu : formula -> formula -> formula
| MonNon : formula -> formula.
Fixpoint eval (F : formula) : bool :=
  match F with
    | MonTrue => true
    | MonFalse => false
    | MonEt F1 F2 => if eval F1 then eval F2 else false
    | MonOu F1 F2 => if eval F1 then true else eval F2  
    | MonNon F' => negb (eval F')
  end.
Eval compute in (eval (MonOu (MonEt MonTrue MonFalse) (MonTrue))).



(****************************)
(** * III : Prouver en Coq **)
(****************************)
(** Dans la première partie, on va découvrir ce qu'est une preuve en Coq. Ca risque
d'être un peu cosmique. Pour bien comprendre, il vaut mieux avoir entendu parler de la 
correspondance de Curry-Howard (cf. les références données sur ma page et le cours de lambda-calcul).
Mais pas de panique, dans la section suivante on va voir comment s'aider des tactiques les plus
importantes. Dans la dernière section on verra l'induction.*)

(** ** 1. Une preuve en Coq **)
(*****************************)

(** Le but ici est de comprendre l'objet preuve de Coq.
On va prouver quelques lemmes complètement triviaux et ça vous paraîtra
compliqué mais le but est de comprendre ce qu'il se passe quand plus tard
vous prouverez des théorèmes plus compliqués en utilisant de grosses tactiques.*)

  (** En fait on a déjà écrit des preuves: [f:A] est une fonction de type A mais en Coq
on peut aussi appeler ça une preuve de la formule logique A : c'est la correspondence de Curry-Howard.
En résumé, une preuve Coq de la formule [A] c'est un terme de type [A]. *)
Check True.
(** [True] est un terme de type [Prop] c'est donc aussi une formule.
      A ne pas confondre avec le booléen [true]. *)
(** On va prouver notre premier lemme: *)
Lemma tauto1 : True.
  (** On veut prouver [True], ça va être facile. En déduction naturelle, il existe la règle
        Intro Top, en Coq on peut regarder ce que siginifie [True] et [False]:*)
  Print True. Print False.
  (** [True] est la formule qui n'a qu'un habitant [I] (traduction: le seul terme de type [True]
        est [I]). Prouver [True] revient à donner [I] qui a le bon type [I:True]. Bien sûr, [False]
        n'a pas d'habitant: on ne peut pas le prouver.*)
  apply I.
  (** La preuve est complète comme nous l'indique Coq.*)
Qed.
(** [Qed] demande à Coq de clore la preuve (une fois que tous les buts ont été prouvés). Coq construit alors
le terme correspondant et lui donne le nom du lemme.*)
Print tauto1.
(** Résumé de cette magnifique preuve:
        tauto1 est une preuve de True (= tauto1 est la fonction I de type True).
        On a prouvé True car on a construit un terme habitant dans ce type. *)

Lemma tauto2 (A B : Prop): A -> B -> A /\ B.
  (**
Voici quelques règles générales sur la construction de preuves en Coq:
 - Coq nous indique le nombres d'objectifs (cad. de preuves à construire) avant de pouvoir clore la preuve (ici un objectif sur un total d'un),
 - Pour chaque objectif, on visualise le but (sous la ligne continue) et les hypothèses
   que l'on a à disposition. En déduction naturelle, on a [Gamma |- P] alors qu'en Coq, on a:
<<
            Gamma
            _______ (1/1)
            P
>>
 - La construction de la preuve est dirigée par le but (ce qu'il faut montrer) un peu comme en déduction naturelle. On ne construit donc pas la preuve en partant des axiomes. Toutefois, on verra que l'on peut manipuler les axiomes plus facilement qu'en déduction natirelle,
 - On constuit la preuve en donnant à Coq une fonction à appliquer au but (qui va le remplacer par les sous-buts correspondants aux arguments de la fonction). On utilise le mot clé [apply [fonction]],
 - Comme ce n'est pas très pratique (on a vu ça avec [True]), on peut utiliser des tactiques pour s'aider. Il existe de nombreuses tactiques.
   Certaines vont essayer d'appliquer plusieurs fonctions selon la tête du séquent à prouver et permettent donc de gagner beaucoup de 
   temps/lignes. On en verra une petite liste dans la section suivante. Retenez bien qu'une tactique ne fait généralement pas partie de la preuve.
   Elle permet de chercher un terme à appliquer en fonction de la tête du but et des hyptohèses.*)
  (** Ici, on va utiliser la tactique [intro]. Elle correspond à l'introduction de la flèche en déduction naturelle:
<<
         Gamma, P  |-  Q
         -----------------
         Gamma  |-  P -> Q
>>
   *)
  intro. intro. 
  (** Ou plus simplement [intros]. C'est une bonne habitude de nommer les hyptohèses
que l'on charge, ici j'aurais fait [intros HA HB] par ex. On doit désormais prouver une conjonction [/\].
On peut regarder ce que ça signifie. *)
  Locate "/\". Check and. Print and.
  (** [and] a le type [Prop] (c'est donc une formule) qui contient un seul habitant [conj] de type [A -> B -> and A B]. C'est comme cela qu'est encodée la conjonction en Coq. Et donc, pour construire
  un terme de type [and A B] il faut construire des termes de type [A] et [B] et appliquer
cette fonction. *)
  Check conj. Print conj.
  apply conj.
  (** Cette fonction prenait deux arguments: il faut donc construire les termes (= preuves)
pour ces deux arguments, d'où les deux sous-buts que Coq nous demande de prouver. *)
  (** On a le but en hypothèse. Il suffit donc d'appliquer la fonction H (de type A). *)
  apply H.
(** On a prouvé le premier sous-but. Il reste le second sous-but. *)
  apply H0.
Qed.

(** On peut afficher le terme que l'on a construit (vous serez déçu ;) ): *)
Print tauto2.
(** Le terme que l'on a construit est simplement [conj]. On aurait pu pour prouver ce petit lemme
    directement en disant à Coq: "voici un terme habitant dans le type à prouver". On peut le faire
    en utilisant [exact]: *)
Lemma tauto2bis: forall A B : Prop, A -> B -> A/\B.
  exact conj.
Qed.
(** Tout ça fait sens grace à la correspondance de Curry-Howard:
<< Le séquent [Gamma |- A] est prouvable en déduction naturelle intuitionniste
si et seulement s'il existe un lambda-terme [t] tel que [Gamma |- t : A]
(quitte à réindexer Gamma).
>>
Où [Gamma |- t : A] dénote que [t] a le type [A] dans le contexte de typage [Gamma].
*)

(** On va maintenant prouver un lemme un poil plus compliqué. Mais cette
      fois, je vais utiliser des tactiques et on regardera le terme produit. *)
Lemma tauto3 : forall A B : Prop, A/\B -> B/\A.
  intros A B H.
  (** On NOMME ces hypothèses *)
  destruct H.
  split.
  apply H0.
  apply H.
Qed. Print tauto3.
(** Ouf, comment on a fait ce pattern-matching? *)
(** H est de type [and] qui ne contient que le constructeur conj, on peut donc
réaliser un pattern-macthing sur le terme H. C'est ce que fait [destruct]: il n'y
a qu'un pattern possible (car il n'y a qu'un seul habitant dans [and A B]) et on récupère
les deux hypothèses [A] et [B] venant des arguments de conj.
On remarque qu'ici, destruct fait la même chose que la règle de la conjonction gauche du calcul des séquents:
<<
         Gamma, A, B  |-  Q
         ------------------
         Gamma, A/\B  |-  Q
>>*)

(** Ensuite [split] va appliquer la fonction constructeur associée au but (ici c'est la fonction conj) et
donc générer les deux sous-buts correspondant à ses arguments.
[split] correspond donc à la règle de l'introduction de la conjonction en déduction naturelle:
<<
         Gamma |-  P    Gamma |-  Q
         --------------------------
         Gamma |-  P/\Q
>>
Et on conclut avec l'application des hypothèses.*)

(** On peut aussi réutiliser un lemme déjà prouvé (ça revient à appliquer le terme construit
lors de la preuve de ce lemme).*)
Lemma tauto3' : forall A B : Prop, A/\B -> B/\A.
  intros A B AB.
  (** On NOMME ces hypothèses *)
  destruct AB.
  apply tauto2.
  apply H0. apply H.
Qed.


(** ** 2. Tactiques principales **)
(*********************************)
(** On peut s'amuser à construire le terme qui a exactement le bon type.
Mais Coq nous permet de construire la preuve/fonction de façon interactive. Et c'est de cette façon
qu'on écrira des preuves plus tard. On va se servir du "Coq cheat sheet" pour prouver quelques propriétés
de logique propositionnelle.
Prenez la page 2 de ce document.
 *)
Lemma or_comm : forall A B, A\/B -> B\/A.
Proof.
  intros A B AoB.
  destruct AoB.
  Print or.
  (** Et oui, si on fait [Print or] alors on se rend compte que le type [or] contient
   deux habitants (les deux projections): [or_introl : A -> A \/ B] et [or_intror : B -> A \/ B].
   Donc [destruct] va faire le pattern-matching de ces deux cas ce qui aura pour effet
   de créer deux sous-buts suivant le pattern choisi. C'est exactement la règle de la disjonction gauche
   (\/ left) du calcul des séquents. *)
  right. auto.
  (** On a simplement choisi quelle côté de la disjonction on voulait prouver (comme le permet les deux règles
de l'introduction de la disjonction (\/I1 et \/I2) de la déduction naturelle par exemple) et on a invoqué
une hypothèse. [auto] est une tactique qui va chercher dans les hypothèses s'il n'y a pas directement le but. *)
  left. auto.
Qed.
Print or_comm.

(** On va définir le prédicat "si et seulement si". On appelle "prédicat" un objet qui renvoie
 un [Prop] (une formule). *)
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
(** On va maintenant prouver quelques lemmes sur ce prédicat. *)
Lemma iff_implies : forall P Q, iff P Q -> (P -> Q).
Proof.
  intros P Q H.
  (** Quand une hypothèse (ou la conclusion) contient une formule dont vous avez oublié la définition, vous pouvez l'unfolder de cette façon:  *)
  unfold iff in H.
  destruct H as [HPQ HQP].
  (** Le [as [nom1 nom2]] me permet de nommer les hypothèses générées par le [destruct]: c'est une
   bonne habitude de tout nommer. *)
  auto.
Qed.

Lemma iff_sym : forall P Q, (iff P Q) -> (iff Q P).
Proof.
  intros P Q H.
  destruct H as [HPQ HQP].
  split; auto. 
(** Dans la ligne précédente j'utilise le point virgule entre split et auto pour demander à Coq
 d'appliquer automatiquement [auto] à tous les sous-buts générés par [split]. Le point virgule est très
utile pour automatiser certaines tâches redondantes.*)
Qed.

(** **** Question 6:*)(** Prouvez les lemmes suivants:*) 


(** On définit maintenant le prédicat sur les entiers "est un entier pair". Pour constuire
un prédicat en Coq, il faut:
  - lui donner un nom et un type (ici [even : nat -> Prop],
  - définir les règles d'inférences (et leur donner des noms) qui permettent de définir ce prédicat.
    Dans notre cas, il y en a deux que l'on nommera even0 et evenS. La première dit simplement que 0 est
    pair (sans autre hypothèse). La seconde dit que sous l'hypothèse que [x] est pair alors [x+2] est pair.*)
Inductive evenP : nat -> Prop :=
  even0 : evenP 0
| evenS : forall x:nat, evenP x -> evenP (S (S x)).

(** Cette définition est la traduction en Coq du prédicat [evenP] défini avec les règles d'inférences suivantes:
<<
                         evenP x
--------- even0    et    ------------ evenS
evenP 0                  evenP (x+2)
>>
 *)
(** Attention: en écrivant ce type de données, on n'a pas prouvé que tout entier était pair. On a construit
un terme qui prend un entier et qui renvoie la formule qui dit "l'entier est pair".
Le lemme (faux) qui dit que tout entier est pair est [forall n, evenP n].*)
(** **** Question 7:**) (** Prouvez maintenant que deux est pair: *)

Lemma two_even : evenP (S (S 0)).
Proof.
apply evenS.
apply even0.
Qed.

Print two_even.

(** **** Question 8:**) (** Définissez le prédicat "plus petit que" de type [nat -> nat -> Prop].
Quelle est la différence avec ce que vous avez écrit pour la question 5 ?
Prouvez que 3 et plus petit que 6.*)

Inductive less_than : nat -> nat -> Prop := 
  less0 : forall n : nat, less_than 0 n 
  |lessS : forall (n m:nat), less_than n m -> less_than (S n) (S m).

Lemma three_less_than_six : less_than 3 6.
Proof.
apply lessS. apply lessS. apply lessS.
apply less0.
Qed.
(** **** Question 9:**) (** Définissez le prédicat "estTrie" de type [list nat -> Prop].
Prouvez que [3 :: 6 :: nil] estTrie. *)

(** ** 3. Preuves inductives et recherche de lemmes **)
(*****************************************************)
(** Si on veut montrer, par exemple, que [n+1] n'est pas pair si [n] est pair alors on va avoir
besoin de raisonner par induction (vous en êtes convaincu?).
Ca tombe bien parce que quand on définit un objet inductif,
Coq nous fournit automatiquement un axiome d'induction structurelle. Pour les entiers c'est: *)
Check nat_ind.
(** C'est bien le schéma par induction habituel: on peut donc appliquer ce terme quand on veut
   faire une induction ou alors, de façon équivalente, appeler la tactique [induction].
On va s'en servir dans la preuve suivante. *)
Require Import Arith.
Lemma sum_even : forall n,  evenP n -> ~ evenP (S n).
Proof.
  intros n En.
  unfold not.
  intro ESn.
  (** On va faire une induction sur n: *)
  induction n.
  (** On doit traiter le cas n=0 (initialisation): *)
  (** Dans ce cas, on se rend compte que ESn n'est pas possible. On va utiliser
   la tactique [inversion] qui va traiter les différents cas possibles de evenP
   en éliminant ceux qui sont impossibles. *)
  inversion ESn.
  (** Cas inductif: on commence par utiliser l'hypothèse d'induction. *)
  apply IHn.
  (** On sait que n+2 est pair: on va donc inverser ESn et on aura que n est pair *)
  inversion ESn.
  auto.
  auto.
Qed.
(** [nat_ind] est en fait un lemme qui est automatiquement généré à partir de la définition
    inductive de [nat]. Et ça marche pour tous les prédicats inductifs. Par exemple: *)
Check evenP_ind.
(** On comprend qu'en fait ces lemmes sont des inductions strcuturelles (induction sur la dérivation qui permet de dériver le prédicat. Méditez là-dessus... *)

(** Dans les preuves sur les entiers, on a souvent besoin d'utiliser des axiomes ou de petits
    lemmes triviaux pour réécrire des termes. Regardons cet exemple: *)
Lemma pasSiFacile : forall n, n*2 + 0 = 1 - 1 + n + n.
  intro n.
  (** On a besoin d'expliquer à Coq que le [+ 0] ne sert à rien.
     Pour cela,on va chercher l'axiome qui dit que [n+0=n] (c'est vrai car 0 est le neutre de +, ça fait
parti de l'axiomatisation des entiers dans Coq). On a différentes façons de chercher un lemme dans Coq:
     - [Search [objet]] cherche tous les lemmes prouvant une formule contenant [[objet]];
     - [SearchAbout [formule]] cherche tous les lemmes contenant [[formule]];
     - [SearchPattern [pattern]] cherche tous les lemmes prouvant une formule contenant [[pattern]];
     - [SearchRewrite [pattern]] cherche tous les lemmes dont la conclusion est une égalité contenant [[pattern]].*)
  Search le.
  SearchAbout le.
  SearchRewrite (_ + 0).
  (** On va donc utiliser le lemme [plus_n_O] pour réécrire notre but. On utilise la tactique 
[rewrite] (avec une flèche [<-] si on veut réécrire dans le sens contraire). *)
  rewrite <- plus_n_O.
  (** (On peut aussi utiliser plus_0_r) *)
  SearchRewrite (_ - _).
  rewrite -> (minus_diag 1).
  (** **** Question 10:*)(** Terminez la preuve (sans autre tactique que [rewrite] et [reflexivity]). *) 
Qed.
(**  *)
(** **** Question 11:*)(** Prouvez les lemmes suivants (réfléchissez à la preuve sur papier au préalable et sachez que vous pouvez faire des inductions sur les prédicats inductifs): *) 
Lemma even_double : forall n, evenP n -> exists (m m2 : nat), n = 2*m.
Qed.

Require Import Omega.
(** La tactique [omega] résout tous les problèmes de systèmes d'inéquations et d'équations linéaires. *)
Lemma double_even : forall n, evenP (2*n).
Qed.

Lemma sum_pair : forall n m, evenP n -> evenP m -> evenP (n+m).
Qed.

(** **** Question Bonus (bonus pris en compte pour le projet):*)
(** Prouvez que la fonction de tri que vous avez écrite est correcte
en utilisant le prédicat "estTrie" de la question 9. C'est tout pour la correction? *)
