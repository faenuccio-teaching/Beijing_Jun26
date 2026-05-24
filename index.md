---
# layout: default
# the two items below are only used for `OnlyTheDoc`
# title: "Cours Avancé *Formalisation Mathématique*"
# nav_order: 1
nav_exclude: true
---

# Bienvenue

Ce site contient les informations concernant le Cours Avancé [Formalisation Mathématique](https://www.math.ens.psl.eu/formations/ca-formalisation-mathematique/) pour le M1 du Département de mathématiques et applications de l'ENS-Paris, qui a lieu au deuxième semestre 2025--26.

Le cours est assuré par [Filippo A. E. Nuccio](https://perso.univ-st-etienne.fr/nf51454h/): vous pouvez me contacter [par mail](mailto:filippo.nuccio@univ-st-etienne.fr) et mon bureau est le T8, au quatrième étage. Le matériel est en anglais, le cours aura (probablement) lieu en français. 

Chaque cours vient avec un fichier `.md` (exporté en `.pdf` aussi) que vous trouvez plus bas et qui contient le matériel discuté, ainsi qu'avec un fichier `.lean` à utiliser pendant le cours. Les solutions sont rajoutées le lendemain du cours, en général.

Le `commit` de Mathlib sur lequel ce projet a été développé est le [32d2424](https://github.com/leanprover-community/mathlib4/commits/32d24245c7a12ded17325299fd41d412022cd3fe): la documentation correspondante se trouve [ici](https://faenuccio-teaching.github.io/M1_ENS_26/docs/). Il existe aussi une documentation de [toutes les tactiques](https://leanprover-community.github.io/mathlib4_docs/tactics.html) sur le site officiel de Mathlib.

# Agenda
Les cours ont lieu le mardi de 15h à 18h et le jeudi de 13h30 à 16h30 en Salle Bourbaki selon le calendrier suivant:

| Date      | Cours         | Fichiers annexes | Notes
|-----------|---------------|---------------|---------------
| 3 février | Tactiques et Types | Fichiers [Lean](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/1_Tactics%26Types.lean), [MarkDown](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/1_Tactics%26Types_lecture.md) et [PDF](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/1_Tactics%26Types_lecture.pdf).| 
| 5 février | Types inductifs et structures | Fichiers [Lean](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/2_MoreTypes.lean), [MarkDown](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/2_MoreTypes_lecture.md) et [PDF](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/2_MoreTypes_lecture.pdf)| 
| 10 février | Algèbre 1: Classes, groupes et sous-groupes | Fichiers [Lean](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/3_AlgebraicStructures.lean), [MarkDown](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/3_AlgebraicStructures_lecture.md) et [PDF](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/3_AlgebraicStructures_lecture.pdf)|
| 17 février | Algèbre 2: Sousgroupes et Mathlib | Fichiers du Cours 3|
| 19 février | Algèbre 3: Groupes quotients et Anneaux | Fichiers du Cours 3|
| 10 mars | Ensembles | Fichiers [Lean](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/5_Sets.lean), [MarkDown](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/5_Sets_lecture.md) et [PDF](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/5_Sets_lecture.pdf) |
| 12 mars | **examen** | | Examen écrit de 2h
| 31 mars | séminaires étudiants | • 15h - Paul Landrier (Brownian motion)|  salle R3
| 7 avril | séminaires étudiants | • 13h30 -- Leila Abubakarova (Algebraic Geometry) <br> • 15h00 Bojin Han (Algebraic Geometry)| salle Bourbaki
| **mercredi**<br> 15 avril | séminaires étudiants | • 14h - Yann Didier (Model Theory) <br> • 15h30 - Romane Pagès (Algebra)| salle R3
| **vendredi**<br> 17 avril | séminaires étudiants | • 16h30 - Aimeric Duchemin (Graph Theory) | online


# Références 

Il n'y a pas (encore) beaucoup de livres qui parlent de `Lean`, mais le très beau
* [Mathematical Components](https://math-comp.github.io/mcb/), par A. Mahboubi et E. Tassi, bien que conçu pour l'assistant de preuve [`Rocq`](https://rocq-prover.org/), est une excellente présentation à ce qu'est la formalisation mathématique en général. Le troisième chapitre contient une jolie introduction à la "théorie des types" qu'on utilise.

Un autre résumé de la théorie des types est dans le premier chapitre "Type theory" de
* [Homotopy Type Theory (a.k.a. "HoTT book")](https://homotopytypetheory.org/book/).

Une source plus complète, très bien écrite et fort agréable à lire est
* [Lectures on the Curry–Howard Isomorphism](https://www.sciencedirect.com/bookseries/studies-in-logic-and-the-foundations-of-mathematics/vol/149/suppl/C), par M. H. Sørensen et P. Urzyczyn.

 Les deux références
* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/), par J. Avigad, L. de Moura, S. Kong et S. Ullrich
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), par J. Avigad et P. Massot

    contiennent aussi beaucoup de matériel pertinent pour notre cours.

## Prérequis Lean et Git

Avant le début du cours (le mardi 3 février 2026), assurez-vous de:
* avoir accès à une connexion internet lorsque à l'ENS, idéalement via Eduroam;
* avoir configuré une installation `git`: si vous avez besoin d'aide, vous pouvez vous référer par exemple à la page <a href="https://www.imo.universite-paris-saclay.fr/~patrick.massot/misc/git.html">maintenue par Patrick Massot</a>;
* avoir créé un compte <a href="https://github.com">GitHub</a> pour pouvoir soumettre votre travail;
* installer Lean sur votre ordinateur, en suivant les [instructions officielles](https://lean-lang.org/install/): si vous rencontrez des difficultés, on en parlera lors du premier cours;
* d'avoir créé un `fork` du *repository* en clickant sur le menu déroulant en haut à droite de [cette page](https://github.com/faenuccio-teaching/M1_ENS_26.git), et de l'avoir cloné via `git clone` sur votre ordinateur: pour ce faire, allez sur la page `GitHub` de votre `fork`, clickez sur la flèche verte "Code" et copiez l’adresse. Après, dans votre terminal `Git` (comment y accéder dépend de votre système d'exploitation) tapez `git clone` suivi de l'adresse copiée auparavant. Vous aurez alors un dossier appelé `M1_ENS_26` où vous pourrez travailler;
* d'avoir disabilité toutes les fonctionnalités `Chat` de VSCode: pour ce faire, allez  dans `Settings → Features → Chat` et sélectionnez `Disable AI Features`.
