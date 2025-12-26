Note to readers:
Please ignore these
sidenotes; they’re just
hints to myself for
preparing the index,
and they’re often ﬂaky!

KNUTH

THE ART OF
COMPUTER PROGRAMMING
PRE-FASCICLE 8A
VOLUME 4

HAMILTONIAN
PATHS AND CYCLES

DONALD E. KNUTH Stanford University

ADDISON–WESLEY

December 4, 2025

(cid:0)
(cid:2)(cid:2)

Internet
Stanford GraphBase
MMIX

Internet page https://www-cs-faculty.stanford.edu/~knuth/taocp.html contains
current information about this book and related books.

See also https://www-cs-faculty.stanford.edu/~knuth/sgb.html for information
about The Stanford GraphBase, including downloadable software for dealing with
the graphs used in many of the examples in Chapter 7.

See also https://www-cs-faculty.stanford.edu/~knuth/mmixware.html for down-
loadable software to simulate the MMIX computer.

See also https://www-cs-faculty.stanford.edu/~knuth/programs.html for various
experimental programs that I wrote while writing this material (and some data ﬁles).

Copyright c
(cid:0)

2025 by Addison–Wesley

All rights reserved. No part of this publication may be reproduced, stored in a retrieval
system, or transmitted, in any form, or by any means, electronic, mechanical, photo-
copying, recording, or otherwise, without the prior consent of the publisher, except
that the oﬃcial electronic ﬁle may be used to print single copies for personal (not
commercial) use.

Zeroth printing (revision -56), 03 December 2025

December 4, 2025

BARRY
Internet

PREFACE

But that is not my point.
I have no point.

— DAVE BARRY (2002)

This booklet contains draft material that I’m circulating to experts in the
ﬁeld, in hopes that they can help remove its most egregious errors before too
many other people see it.
I am also, however, posting it on the Internet for
courageous and/or random readers who don’t mind the risk of reading a few
pages that have not yet reached a very mature state. Beware: This material has
not yet been proofread as thoroughly as the manuscripts of Volumes 1, 2, 3, 4A,
and 4B were at the time of their ﬁrst printings. And alas, those carefully checked
volumes were subsequently found to contain thousands of mistakes.

Given this caveat, I hope that my errors this time will not be so numerous
and/or obtrusive that you will be discouraged from reading the material carefully.
I did try to make the text both interesting and authoritative, as far as it goes.
But the ﬁeld is vast; I cannot hope to have surrounded it enough to corral it
completely. So I beg you to let me know about any deﬁciencies that you discover.
To put the material in context, this portion of fascicle 8 previews Section
7.2.2.4 of The Art of Computer Programming, entitled “Hamiltonian paths and
cycles.” I haven’t had time to write much of it yet — not even this preface!

∗

∗

∗

The explosion of research in combinatorial algorithms since the 1970s has
meant that I cannot hope to be aware of all the important ideas in this ﬁeld.
I’ve tried my best to get the story right, yet I fear that in many respects I’m
woefully ignorant. So I beg expert readers to steer me in appropriate directions.
Please look, for example, at the exercises that I’ve classed as research
problems (rated with diﬃculty level 46 or higher), namely exercises 210, 224,
225, . . . ; I’ve also implicitly mentioned or posed additional unsolved questions
in the answers to exercises 65, 231, 369, 370, 372, . . . . Are those problems still
open? Please inform me if you know of a solution to any of these intriguing
questions. And of course if no solution is known today but you do make progress
on any of them in the future, I hope you’ll let me know.

I urgently need your help also with respect to some exercises that I made
up as I was preparing this material. I certainly don’t like to receive credit for
iii

December 4, 2025

Beluhov
SSDIHAM
benchmark graphs
Jelliss
Lefebvre
Stappers
Weigel
Wermuth
Krevl
Roberts
Stanford’s Infolab
Knuth
KNUTH
Ewing

iv

PREFACE

things that have already been published by others, and most of these results are
quite natural “fruits” that were just waiting to be “plucked.” Therefore please
tell me if you know who deserves to be credited, with respect to the ideas found
in exercises 11, 12, 36, 37, 41, 42, 53, 55, 62, 63, 65, 71, 73, 84, 100, 106, 135,
136, 137, 138, 156, 157, 158, 159, 163, 177, 185, 202, 207, 212, 215, 216, 217, 218,
223, 242, 246, 247, 270, 271, 275, 299, 300, 350, 360, 361, 369, . . . . Furthermore
I’ve credited exercises 79, . . . to unpublished work of Nikolai Beluhov and . . . .
Have any of those results ever appeared in print, to your knowledge?

While writing this section I also wrote numerous programs for my own edi-
ﬁcation. (I usually can’t understand things well until I’ve tried to explain them
to a machine.) Most of those programs were quite short, of course; but several
of them are rather substantial, and possibly of interest to others. Therefore I’ve
made a selection available by listing some of them on the following webpage:

https://cs.stanford.edu/~knuth/programs.html

In particular, prototypes of the main algorithms can be found there: Algorithm B
(SSBIDIHAM, and SSDIHAM for the special case of digraphs); Algorithm E
(DYNAHAM) and E
(DYNAHAMP); Algorithm F (HAM-EULER); Algorithm H
(SSHAM); Algorithm W (BACK-WARNSDORF). A few other programs are also
mentioned in the answers to certain exercises.
If you want to see a program
called FOO, look for FOO on that webpage. See also

+

https://cs.stanford.edu/~knuth/programs/ham-benchmarks.tgz

for the benchmark graphs in Table 1.

∗

∗

∗
Special thanks are due to George Jelliss, Arnaud Lefebvre, Filip Stappers, Peter
Weigel, Udo Wermuth, . . . for their detailed comments on my early attempts
at exposition, and to numerous other correspondents who’ve contributed crucial
corrections. Andrej Krevl and Brian Roberts have helped me to utilize hundreds
of core processors on powerful computers in Stanford’s Infolab — quite a thrill!
∗
I happily oﬀer a “ﬁnder’s fee” of $2.56 for each error in this draft when it is ﬁrst
reported to me, whether that error be typographical, technical, or historical.
The same reward holds for items that I forgot to put in the index. And valuable
suggestions for improvements to the text are worth 32/c each. (Furthermore, if
you ﬁnd a better solution to an exercise, I’ll actually do my best to give you
immortal glory, by publishing your name in the eventual book:−)

∗

∗

Cross references to yet-unwritten material sometimes appear as ‘00’; this

impossible value is a placeholder for the actual numbers to be supplied later.

Happy reading!

Stanford, California
99 Umbruary 2016

I have twenty years’ work ahead of me
to ﬁnish The Art of Computer Programming.

D. E. K.

— DONALD E. KNUTH, letter to John Ewing (04 September 1990)

December 4, 2025

GASARCH

CONTENTS

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

.

.

.

.

.
.
.
.
.
.
.
.
.
.

.

.

.

.

.
.
.
.
.
.
.
.
.
.

.

.

.

.

[4A.1]

[4A.281]
[4A.281]
[4B.30]
[4B.65]
[4B.185]
[4fasc7.1]
1
.
2
.
6
.
9
.
11
.
18
.
21
.
30
.
38
.
43
.

.

.

.

.

62

??

107

108

.
.
.
.
.
.
.
.
.
.

.

.

.

.

.
.
.
.
.
.
.
.
.

.

.

.

.

Chapter 7 — Combinatorial Searching .

7.2. Generating All Possibilities

.

.

.

.

.

.

.

.

.

.

.

.
.
.

.
.
.

.
.
.
.

.
.
.
.

7.2.1. Generating Basic Combinatorial Patterns
7.2.2. Backtrack Programming .
.
.

.
.
.
.
7.2.2.1. Dancing links
.
7.2.2.2. Satisﬁability .
.
7.2.2.3. Constraint satisfaction
.
7.2.2.4. Hamiltonian paths and cycles
Hamiltonian paths in antiquity .
.
.
.
A greedy heuristic
.
.
Path ﬂipping .
.
.
.
.
Searching exhaustively .
.
.
A census of knight’s tours
.
Dynamic enumeration .
.
.
Directed and bidirected graphs
.
.
.
History
.
.
.
Exercises

.
.
.
.
.

.
.
.

.
.

.
.

.
.

.
.

.
.

.
.

.
.

.
.

.

.

.

Answers to Exercises

.

.

.

.

.

.

.

Index to Algorithms and Theorems

Answers to Puzzles in the Answers

Index and Glossary .

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

.

I always thought Volume 4 was a myth,
like the missing part of the Dead Sea scrolls.

— BILL GASARCH (blog post, 10 January 2008)

December 4, 2025

v

pinched gasket

December 4, 2025

Plato
HAMILTON
BERGHOLT
EULER
Hamilton
quaternions
Platonic solids
icosahedron
Icosian Game
planar graph
dual of a planar graph
dodecahedron

7.2.2.4

HAMILTONIAN PATHS AND CYCLES

1

A long train of consistent calculations opens itself out,
for every result of which there is found a corresponding
geometrical interpretation, in the theory of two of the celebrated
solids of antiquity, alluded to with interest by Plato in the Timæus;
namely, the Icosaedron, and the Dodecaedron.

— WILLIAM ROWAN HAMILTON (1856)

The total number of possible [knight’s] tours that can be made is so vast that
it is safe to predict that no mathematician will ever
succeed in counting up the total.

— ERNEST BERGHOLT (1915)

I’ll show that this problem is susceptible to a very special analysis,
which merits extra attention because it involves reasoning of a kind rarely used
elsewhere. The excellence of Analysis is easy to see, but most people think that
it’s limited to traditional questions about Mathematics; hence it will always be
quite important to apply Analysis to subjects that seem to make it out of reach,
for it incorporates the art of reasoning in the highest degree.
One cannot then extend the bounds of Analysis
without justiﬁably expecting great advantages.

— LEONHARD EULER (1759)

7.2.2.4. Hamiltonian paths and cycles. A path or cycle that touches every
vertex of a graph is called “Hamiltonian” in honor of W. R. Hamilton, who began
to ponder and publicize such questions shortly after discovering the quaternions.
Hamilton was fascinated by Platonic solids such as the icosahedron, with its 20
triangular faces; and he introduced what he called the Icosian Game, based on
paths that go from face to face in that solid. Equivalently (see Fig. 121), his game
was based on paths from vertices to vertices along the edges of a dodecahedron.

43

32

24

14

21

13

31

45

12

41

21

42

34

23

(a) Icosahedron;

32

14

13

51

24

43

25

12

35

53

34

52

42

31

41

54

23

15

(b) Dodecahedron.

Fig. 121. The icosahedron and dodecahedron, whose vertices, edges, and faces deﬁne
“dual” planar graphs: The faces of one solid correspond to the vertices of the other.
(The vertices have been named with two-digit codes that are discussed in exercise 3.)

December 4, 2025

2

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

It’s convenient to redraw Fig. 121(b) as three concentric rings, without
crossing edges, as shown in Fig. 122(a). Then it’s easy to ﬁnd a Hamiltonian
cycle, such as the one indicated by bold edges in Fig. 122(b). (In fact, Hamilton
proved that every such cycle on the dodecahedron is essentially the same as
this one; see exercise 9.) Thus we can also redraw the dodecahedron’s graph as
shown in Fig. 122(c). From that diagram it’s obviously Hamiltonian — that is,
it obviously has a spanning cycle; but it’s not obviously planar at ﬁrst glance.

13

32

45

21

52

24

51

14
53

25
31

42

43

12

35

13

32

45

54

21

24

51

14
53

25
31

42

34

23

34

23

15

(a)

41

52

15

(b)

43

12

35

54

41

12

54

43

51

32

45

23

41

35

24

21

53

14

25

13

52

34

15

(c)

31

42

concentric rings
Hamilton
spanning cycle
chords
3-regular graph
trivalent graphs
cubic graph
NP
Ham paths, history of–
Graeco-Roman icosahedra
Greek alphabet
Michon
Louvre
Perdrizet
British Museum
author

Fig. 122. Alternative views of a dodecahedron’s vertices and edges.

Every Hamiltonian graph can clearly be drawn as a great big cycle, together
with “chords” between certain pairs of vertices that aren’t neighbors in the cycle.
Thus a 3-regular graph can be speciﬁed compactly by listing only a third of its
edges, if it is Hamiltonian. (On the other hand, many trivalent graphs are not
Hamiltonian. In fact, the task of deciding whether or not a given cubic graph is
Hamiltonian turns out to be NP-complete; see exercise 14.)

Hamiltonian paths in antiquity. Let’s take a moment to discuss the rich
history of the subject before we consider techniques by which Hamiltonian paths
and cycles can be found. A strong case can actually be made for the assertion
that questions of this kind represent the birth of graph theory, in the sense that
they were the ﬁrst nontrivial graph problems to be investigated.

For example, museums in many parts of the world contain specimens of
ancient icosahedral objects whose 20 faces are inscribed with the ﬁrst twenty
letters of the Greek alphabet. In most of these cases the alphabetical sequence
A, B, Γ, Δ, . . . , T, Y on such artifacts forms a Hamiltonian path between
[E. Michon, in Bulletin de la Soci´et´e nationale des Anti-
adjacent triangles.
quaires de France (1897), 310 and (1904), 327–329, described an example in the
Louvre, catalog number N 1532; P. Perdrizet, in Bulletin de l’Institut fran¸cais
d’arch´eologie orientale 30 (1930), 1–16, illustrated several others.]

In 2015, curators of the Egyptian antiquities at the British Museum kindly
allowed the author to inspect the four icosahedra in their collection (EA 29418,
EA 49738, EA 59731, EA 59732), of which the ﬁrst three are Hamiltonian. The
experience of rotating them by hand, slowly and systematically according to

December 4, 2025

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: IN ANTIQUITY

3

alphabetic order, turned out to be unexpectedly delightful. Here are views of
the largest one, EA 49738, centered at each of its twelve vertices:

alphabetic order
Pi, as written in Greece
University College London
Petrie
coincidence
Hamilton
reentrant knight’s tour, see closed
Chaturanga
Shat.ranj
knights
al-‘Adl¯ı ar-R¯um¯ı
Ab¯u Zakar¯ıy¯a Yah. y¯a
knight’s tour
Ibn Man¯ı‘
open versus closed tour
closed versus open tour
Murray

It is made of steatite, 5.8 centimeters in diameter and 228 grams in weight, and
was acquired in 1911. A similar example, smaller and with more beautiful let-
terforms, is object number UC 59254 in the nearby Petrie Museum of University
College London [see W. M. F. Petrie, Objects of Daily Use (1927), #288]. What
a pleasant coincidence that W. R. Hamilton himself would independently come
up with the same concept some 1800 years later, and would proceed to ﬁnd a
closed cycle instead of just a path!

Now fast forward to the ninth century, when Hamiltonian paths and cycles
of quite a diﬀerent kind came into play. The game of Chaturanga or Shat.ranj —
a predecessor of chess, having diﬀerent rules for certain pieces, but with knights
moving just as they do today — was becoming popular in Asia. And in A.D. 842
the current world champion, al-‘Adl¯ı ar-R¯um¯ı, published a book about Shat.ranj.
Complete copies of that work are lost; but we know from a subsequent treatise by
Ab¯u Zakar¯ıy¯a Yah. y¯a ibn Ibr¯ah¯ım al-H. ak¯ım that al-‘Adl¯ı had presented a closed
knight’s tour : a Hamiltonian cycle on the chessboard. That same treatise also
recorded an “open” knight’s tour (a Hamiltonian path that can’t be completed
to a cycle), which was credited to an otherwise unknown author Ibn Man¯ı‘.

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:23)

(cid:9)(cid:25)(cid:26)

(cid:9)(cid:27)(cid:8)

(cid:9)(cid:10)(cid:11)

(cid:9)(cid:18)(cid:11)

(cid:9)(cid:22)(cid:5)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:24)(cid:4)

(cid:9)(cid:27)(cid:11)

(cid:9)(cid:28)(cid:23)

(cid:9)(cid:29)(cid:8)

(cid:9)!"

(cid:3)-"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)6"

(cid:2);(cid:26)

(cid:3)<(cid:8)

(cid:9)#$

(cid:3)/0

(cid:7)60

(cid:3)9(cid:5)

(cid:3)(cid:18)$

(cid:9)<$

(cid:3)?(cid:23)

(cid:3)B(cid:8)

(cid:9)?(cid:26)

(cid:3)A(cid:4)

(cid:9)B(cid:4)

(cid:9)C#

(cid:9)D=

(cid:9)EF

(cid:9)G(cid:26)

(cid:3)<(cid:8)

(cid:9)EF

(cid:8)J(cid:19)

(cid:3)NC

(cid:9)O0

(cid:3)QC

(cid:8)SC

(cid:9)O(cid:23)

(cid:3)T(cid:8)

(cid:9)?(cid:26)

(cid:3)A2

(cid:9)I"

(cid:8)J"

(cid:9)LM

(cid:3)QR

(cid:9)S(cid:26)

(cid:3)<(cid:8)

(cid:9)UV

(cid:9)X(cid:23)

(cid:9)BC

(cid:9)YC

(cid:9)X$

(cid:3)QC

(cid:9)Z(cid:23)

(cid:3)[(cid:8)

Ibn Man¯ı‘:

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)E"

(cid:8)Z(cid:19)

(cid:0)Q2

(cid:9)]=

(cid:8)G(cid:26)

(cid:3)^(cid:8)

al-‘Adl¯ı:

(cid:9)(cid:10)(cid:31)

(cid:9)(cid:18)(cid:31)

(cid:3)](cid:4)

(cid:3)(cid:10)C

(cid:9)S(cid:4)

(cid:9)(cid:10)V

(cid:9)_(cid:23)

(cid:3)6(cid:8)

(1)

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)_F

(cid:9)a"

(cid:9)b=

(cid:9)cF

(cid:9)G(cid:26)

(cid:3)<(cid:8)

(cid:9)#V

(cid:3)YC

(cid:3)Z0

(cid:9)(cid:28)$

(cid:3)(cid:18)0

(cid:9)6b

(cid:3)c(cid:23)

(cid:3)6(cid:8)

(cid:9)d(cid:4)

(cid:8)f(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g=

(cid:9)i[

(cid:3)j(cid:8)

(cid:9)EC

(cid:8)X(cid:31)

(cid:9)NC

(cid:3)d0

(cid:8)e(cid:4)

(cid:8)gC

(cid:9)X7

(cid:3)h(cid:8)

(cid:9)k"

(cid:9)m"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)nR

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)U$

(cid:9)JC

(cid:9)jC

(cid:9)UC

(cid:9)X$

(cid:9)ǱV

(cid:9)j2

(cid:9)l(cid:8)

[See H. J. R. Murray, A History of Chess (Oxford, 1913), 175–176, 336.] These
remarkable constructions are the earliest known solutions to what was destined
to become a classic combinatorial problem. It seems likely that the ﬁrst path was
discovered before the ﬁrst cycle, because there are so many more of the former.

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
’
(
)
*
+
,
(cid:0)
(cid:7)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
(cid:11)
.
&
3
/
)
4
0
5
(cid:2)
(cid:7)
(cid:29)
(cid:19)
(cid:20)
7
3
(cid:21)
8
)

(cid:16)
9
(cid:24)
:
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:4)
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
(cid:30)
(cid:14)
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:12)
%
(cid:6)
(cid:13)
(cid:14)
)
(cid:16)
9
(cid:24)
:
>
(cid:11)
(cid:26)
.
(cid:13)
8
K
(cid:15)
5
(cid:0)
(cid:7)
.
N
O
8
*
P
(cid:0)
>
(cid:29)
(cid:26)
3
(cid:13)
K

(cid:7)
(cid:8)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
2
(cid:11)
(cid:19)
$
%
3
N
(cid:14)
V
4
W
9
X
Y
[
T
&
N
(cid:21)
/
W
\
(cid:24)
,
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
%
H
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
(cid:30)
K

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:19)
(cid:6)
(cid:20)
(cid:15)
(cid:21)
(cid:2)
(cid:8)
(cid:19)
(cid:6)
(cid:20)
(cid:2)
(cid:8)
(cid:3)
(cid:23)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:25)
(cid:6)
(cid:14)
(cid:16)
(cid:26)
(cid:2)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:19)
(cid:13)
(cid:20)
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:30)
(cid:31)
(cid:5)

!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
(cid:23)
&
’
(
)
*
+
,
-
.
(cid:0)
(cid:7)
1
(cid:23)
&
2
(
)
3
!
(cid:15)
,
4
(cid:21)
5
(cid:0)
(cid:31)
(cid:5)
7

8
(cid:20)
!
"
,
5
(cid:8)
(cid:23)
&
’
(cid:6)
)
,
:
.
(cid:7)
(cid:8)
%
(cid:31)
(cid:23)
;
(cid:13)
+
"
(cid:7)
(cid:8)
(cid:3)
0
(cid:31)
(cid:5)
&
=
(

8
3
+
"
,
-
>
(cid:7)
&
@
)
A
,
:
.
(cid:0)
(cid:7)
(cid:9)
(cid:7)
C
0
D
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:31)
1
(cid:25)
&
’
G
;
8
(cid:14)
H
I
:
(cid:17)
.
’
K
(cid:20)
*
L
M
(cid:0)
(cid:2)
0
(cid:31)
G
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
P
&
’
G
;
8
!
"
,
:
.
(cid:7)
(cid:8)
(cid:12)
&
’
)
(cid:14)
R
:
(cid:26)
>
(cid:0)
0
(cid:31)
G
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
&
’
G
)
,
:
.
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
C
F
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
K
*
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
(cid:13)
A
(cid:0)
(cid:7)
(cid:3)
(cid:23)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:31)
G
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
’
G
W
:
M
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:31)
(cid:25)
2
;
(cid:14)
A
"
(cid:16)
(cid:26)
(cid:2)
’
G
(cid:13)
:
M
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)

(cid:13)
(cid:14)
\
(cid:16)
(cid:17)
(cid:8)
(cid:23)
(cid:19)
’
;
(cid:13)
(cid:20)
"
:
M
(cid:8)
(cid:5)
’
(cid:6)
:
M
(cid:2)
(cid:7)
(cid:8)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:26)
(cid:0)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:31)
(cid:5)
(cid:25)
^
(cid:14)
W
"
(cid:16)
(cid:26)
(cid:2)
(cid:8)
@
(cid:13)
A
:
M
(cid:0)
(cid:7)
(cid:9)
(cid:7)
(cid:30)
(cid:31)
(cid:5)

!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
0
(cid:31)
(cid:23)
&
’
(
;
)
*
‘
"
,
-
.
(cid:7)
&
=
8
A
,
:
>
(cid:0)
(cid:7)
(cid:31)
(cid:5)
(cid:23)
^
(cid:13)
!
"
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:23)
&
’
(cid:6)
a
W
,
:
>
(cid:7)
(cid:8)
(cid:23)
2
(cid:13)
A
!
(cid:0)
(cid:7)
(cid:3)
0
(cid:31)
(cid:5)
&

8
+
"
,
5
(cid:7)
(cid:8)
&
@
)
A
,
:
.
(cid:0)
(cid:7)
(cid:9)
(cid:7)
C
0
D
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
1
(cid:25)
&
’
G
8
(cid:14)
(cid:15)
I
:
(cid:17)
.
(cid:0)
1
(cid:19)
G
;
(cid:20)
\
(cid:21)
(cid:2)
(cid:8)
0
(cid:31)
(cid:19)
’
;
(cid:20)
!
"
:
M
(cid:2)
(cid:8)
D
1
&
’
G
;
8
!
\
,
:
(cid:21)
>
(cid:7)
(cid:25)
7
’
8
f
R
:
(cid:26)
.
(cid:0)
0
(cid:31)
1
(cid:25)
G
;
(cid:14)
!
H
(cid:16)
(cid:17)
(cid:2)
(cid:8)
’
G
8
(cid:20)
,
:
.
(cid:0)
(cid:8)
(cid:9)
(cid:7)
C
F
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
F
K
*
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
(
i
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
F
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
K
*
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
F
G
W
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(
i
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
G
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
4

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

Remarkably, knight’s tours on half of a chessboard, 4×8, had been published
even earlier, by Kashmiri poets who were famous for their wordsmithing skills:

Rudrat.a
Ratn¯akara
slokas
fractured English

(cid:9)B(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:18)p

(cid:9)q(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)Ip

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)(cid:10)(cid:4)

(cid:9)C(cid:11)

(cid:9)(cid:25)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)Cp

(cid:9)|p

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

Rudrat.a
(c. 815)

(cid:9)(cid:10)"

(cid:8)-"

(cid:3)1"

(cid:9)u#

(cid:3)1"

(cid:9)v"

(cid:3)w(cid:26)

(cid:3)L(cid:8)

(cid:9)EF

(cid:8)d(cid:11)

(cid:9);>

(cid:9)gU

(cid:8)](cid:4)

(cid:8)g=

(cid:9)a[

(cid:3)j(cid:8)

Ratn¯akara
(c. 830)

(cid:9)!"

(cid:3)-"

(cid:3)w#

(cid:9)n"

(cid:3)-"

(cid:9)1>

(cid:7)u(cid:26)

(cid:3)s(cid:8)

(cid:9)E=

(cid:8)z>

(cid:9)g=

(cid:8)i(cid:4)

(cid:3)(cid:22)#

(cid:9)~=

(cid:9)z[

(cid:3)j(cid:8)

(2)

(cid:9)k"

(cid:9)m"

(cid:9)y#

(cid:9)nR

(cid:9)z"

(cid:9)nR

(cid:9){.

(cid:9)o(cid:8)

(cid:9)k"

(cid:9)m#

(cid:9)1R

(cid:9)a.

(cid:9)y"

(cid:9)(cid:127)R

(cid:9){.

(cid:9)b(cid:8)

Two copies of Rudrat.a’s half-tour will make an open tour on the full board. And
◦
.
two copies of Ratn¯akara’s will make a closed tour, if we rotate one copy by 180
Sanskrit poems traditionally consisted of verses called slokas, containing 32
syllables each. Here is sloka number 15 in chapter 5 of Rudrat.a’s K¯avy¯ala ˙nk¯ara:
(cid:0)(cid:2)(cid:3)(cid:4) (cid:5)(cid:6)(cid:5)(cid:6)(cid:5)(cid:6)(cid:3)(cid:4) (cid:3)(cid:4)(cid:5)(cid:6) (cid:5)(cid:6)(cid:3)(cid:4)(cid:3)(cid:4) (cid:3)(cid:4)(cid:3)(cid:4)(cid:5)(cid:6)(cid:5)(cid:6)(cid:5)(cid:6) ।
(cid:3)(cid:4)(cid:5)(cid:6)(cid:3)(cid:4)(cid:5)(cid:6)(cid:0)(cid:5) (cid:3)(cid:4)(cid:5)(cid:6)(cid:3)(cid:4) (cid:5)(cid:6)(cid:5)(cid:6)(cid:5)(cid:6) (cid:3)(cid:4)(cid:3)(cid:4)(cid:3)(cid:4)(cid:3)(cid:4)(cid:5)(cid:6) ॥ 1-॥

sen¯a l¯ıl¯ıl¯ın¯a n¯al¯ı l¯ın¯an¯a n¯an¯al¯ıl¯ıl¯ı
n¯al¯ın¯al¯ıle n¯al¯ın¯a l¯ıl¯ıl¯ı n¯an¯an¯an¯al¯ı [15]

This enigmatic text, which speaks of military leadership, sounds almost like
gibberish. But it cleverly represents a knight’s tour, in the same way that his
sloka 14 had represented a rook’s tour: When we read those 32 syllables in order
of the left tour in (2), we get exactly the same words!

More precisely, consider the following two 4 × 8 arrays of syllables σj:
σ1 σ30 σ9 σ20 σ3 σ24 σ11 σ26
σ16 σ19 σ2 σ29 σ10 σ27 σ4 σ23
σ31 σ8 σ17 σ14 σ21 σ6 σ25 σ12
σ18 σ15 σ32 σ7 σ28 σ13 σ22 σ5

σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8
σ9 σ10 σ11 σ12 σ13 σ14 σ15 σ16
σ17 σ18 σ19 σ20 σ21 σ22 σ23 σ24
σ25 σ26 σ27 σ28 σ29 σ30 σ31 σ32

(3)

The subscripts on the left correspond to the ﬁrst sequence of knight moves in (2),
while the subscripts on the right have their natural order. Rudrat.a composed a
verse with the amazing property that both arrays agree (with σ1 = σ1, σ30 = σ2,
σ9 = σ3, . . . , σ5 = σ32), by choosing σ1 = (cid:0)(cid:2), σ2 = (cid:3)(cid:4), σ3 = σ4 = σ5 = (cid:5)(cid:6), etc.

Notice that the constraints forced him to use at most four diﬀerent symbols,
thereby throwing away most of the tour’s structure. It turns out, in fact, that
there are two knight’s tours consistent with his sloka. Therefore nobody knows
whether he was thinking of the tour in (2) and (3) or the tour in exercise 36(i).
Thousands of 4 × 8 knight’s tours are possible, and if Rudrat.a had known
more of them he could have written a much less ambiguous sloka that had twelve
distinct syllables. For example, a “fractured English” verse that describes such
a poet-friendly tour might go like this (see exercise 36(ii)):

Want a good, good time, lots of fun?
Now not time so good; now not time.
Foo. Ah, so! So now fun is lost.
Time not now good, so time not now.

(4)

Ratn¯akara came up with a better idea a few years later. For his tour,
illustrated at the right of (2), he composed two diﬀerent slokas, both of which
made sense as part of his overall poem. Their syllable patterns

σ26 σ11 σ24 σ5 σ20 σ9 σ30 σ7
σ23 σ4 σ27 σ10 σ29 σ6 σ19 σ16
σ12 σ25 σ2 σ21 σ14 σ17 σ8 σ31
σ3 σ22 σ13 σ28 σ1 σ32 σ15 σ18

σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8
σ9 σ10 σ11 σ12 σ13 σ14 σ15 σ16
σ17 σ18 σ19 σ20 σ21 σ22 σ23 σ24
σ25 σ26 σ27 σ28 σ29 σ30 σ31 σ32

(5)

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
2
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:12)
%
3
(cid:13)
(cid:14)
)

(cid:16)
9
(cid:24)
:
#
7
&
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:5)
.
&
(cid:6)
/
K
0
(cid:2)
(cid:7)
(cid:3)
$
.
N
8
*
P
(cid:0)
(cid:7)
(cid:28)
(cid:26)
&
(cid:13)
(
V
0
(cid:0)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
$
.
&
(cid:30)
N
/
K

*
0
P
(cid:7)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
)
(cid:15)
W
9
X
Y
(cid:0)
(cid:19)
(cid:20)
.
x
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:4)
(cid:20)
O
(cid:31)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
@
3
N
(cid:14)
h
e
(cid:17)
P
(cid:19)
(cid:20)
%
x
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
@
3
(cid:14)
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:23)
(cid:20)
(cid:13)
(cid:21)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:26)
$
%
&
3
’
(
)

*
+
,
(cid:7)
(cid:5)
T
&
(cid:6)
/
)
\
:
(cid:2)
(cid:7)
(cid:29)
.
3
8

(cid:2)
(cid:7)
(cid:3)
#
(cid:26)
%
&
(cid:13)
(
)
+
:
(cid:0)
(cid:7)
}
.
&
/
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
p
$
.
&
(cid:30)
N
t
(cid:31)
4
*
0
5
P
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:4)
(cid:11)
(cid:20)
O
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:29)
(cid:11)
(cid:19)
M
3
N
x
h
e
(cid:17)
P
(cid:20)
%
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:19)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
‘
3
(cid:14)
(
(cid:31)
h
(cid:16)
0
(cid:17)
(cid:2)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
poetic license
Rudrat.a
Ratn¯akara
Bhoja
De´sika
Someshvara III
nonsense verse
doggerel
Yah. y¯a ibn Ibr¯ah¯ım
abjad numerals

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: IN ANTIQUITY

5

would have allowed him to deﬁne a tour quite precisely using 32 distinct syllables.
(See his Haravijaya, Chapter 43, slokas 145 and 146.) For example, here’s an
English rendition of his two-sloka scheme:

Have some fun, watch this or that word —
Great four lines, take out, each gives eight.
Left; then two black; and just here white.
Three rook steps make one knight move, right?

One, two, three, four! Watch each word here;
Or take some left steps and move eight.
Just right gives this black rook great fun,
Then have lines make out that white knight.

(6)

We obtain the second verse by reading the ﬁrst verse in knight’s tour order,
starting at the ﬁfth syllable of the fourth line. (Ratn¯akara actually used only 24
diﬀerent syllables. Furthermore, his choices for σ5 and σ32 did not agree in the
two slokas; this may be due to errors in transmission of the ancient text, or to
“poetic license.” In any case his remarkable poem clearly deﬁned a knight’s tour.)
Such wordplay had many devotees in medieval India. For example, Rudra-
t.a’s tour of (2) was rendered in Ratn¯akara’s two-sloka style by King Bhoja in
his Sarasvat¯ı-kan. t.h¯abharan. a (c. 1050), slokas 2.306 and 2.308; also by Ved¯anta
De´sika in his devotional hymn P¯aduk¯asahasra (1313), slokas 929 and 930.

A simpler scheme, capable of encoding knight’s tours on the full 8 × 8 board,
was used in slokas 5.623–632 of the encyclopedic Sanskrit work M¯anasoll¯asa by
King Someshvara III (c. 1130). He named each square of the board systematically
by combining a consonant for the column with a vowel for the row; then an arbi-
trary tour was a nonsense verse of 64 syllables, which could be memorized if you
wanted to impress your friends. For example, in English we could use the names

fee

foe

fay

bah bay bee boe boo buh bai bao
dah day dee doe doo duh dai dao
fao
fah
hah hay hee hoe hoo huh hai hao
lah
lao
mah may mee moe moo muh mai mao
nah nay nee noe noo nuh nai nao
sao
sah say

suh sai

fuh

soo

luh

soe

foo

loo

see

lay

loe

lee

fai

lai

⎤

⎥
⎥
⎥
⎥
⎥
⎥
⎥
⎥
⎦

⎡

⎢
⎢
⎢
⎢
⎢
⎢
⎢
⎢
⎣

to encode Someshvara’s tour as the following (memorable?) quatrain:

Sah nee soo nai lao fai bao duh, foe boo dee bah fay lah nay soe;
nuh sao mai hao dai huh doo bee, dah hay mah say noe suh nao lai.
Fao bai fuh dao buh doe bay fah, lay nah see noo sai mao hai foo?
Luh moe hee loo mee hoe moo lee, hoo fee boe day hah may loe muh.

(7)

(8)

Incidentally, Yah. y¯a ibn Ibr¯ah¯ım had presented the two knight’s tours in (1)
by ﬁrst stating two 64-word poems in Arabic, then copying the words of those
poems into 8 × 8 diagrams, according to the knight’s paths. Then he repeated
the right-hand tour, using the Arabic words “ﬁrst,” “second,” . . . , together
with Persian-style abjad numerals, in place of the words of the corresponding

December 4, 2025

John Rylands Library
Path diagrams
dalla Volpe
greedy
heuristic
greedy algorithms
Warnsdorf–

6

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

poem. [His work is preserved in a rare manuscript belonging to the John Rylands
Library in Manchester: Arabic MS. 766, folio 39.] The latter convention, which
corresponds to

60 11 56 7 54 3 42 1
57 8 59 62 31 64 53 4
12 61 10 55 6 41 2 43
9 58 13 32 63 30 5 52
34 17 36 23 40 27 44 29
37 14 33 20 47 22 51 26
18 35 16 39 24 49 28 45
15 38 19 48 21 46 25 50

(9)

in decimal notation, has been used by many subsequent authors to characterize
particular knight’s tours in an easy-to-understand way. Path diagrams such as
(1) and (2), which provide complementary insights, weren’t invented until much
later, when Lelio dalla Volpe published a short book Corsa del Cavallo per tutt’ i
scacchi dello Scacchiere (Bologna, 1766), containing nineteen examples.

A greedy heuristic. Early in the 1800s, the knight’s tour problem inspired
an important new approach to combinatorial problems, based on making a
sequence of locally optimum decisions. Such techniques, now known as “greedy
algorithms,” were unheard-of at the time. But H. C. von Warnsdorf, a high court
oﬃcial in Hesse who had challenged himself by spending many nights trying to
construct long paths of a knight, hit on a simple idea that worked like magic: At
each step, move to a place that has the fewest remaining exits. This principle
has become famous as “Warnsdorf’s rule.”

For example, suppose we want to construct an open knight’s tour on a 5 × 5
board, starting in a corner. Numbering the cells ij for 0 ≤ i, j < 5, we can
assume by symmetry that the ﬁrst two steps are 00 −−−12. From cell 12 we can
move the knight to either 04, 24, 33, 31, or 20, from which it could then exit in
either 1, 3, 3, 3, or 3 ways; Warnsdorf’s rule tells us to choose 04, because 1 < 3.
(Indeed, this is our last chance to visit 04, unless the tour will end at that cell.)
After 04 the knight must proceed to 23; and again we have ﬁve choices, namely
44, 42, 31, 11, or 02. The rule takes us to 44, then 32; then to 40, then 21; and
we’ve completed a partial tour that looks like this:

1 3 2 3 3
3 2 2 2 3
2 8 8 4 2
3 2 6 2 3
7 3 2 3 5

(Bold numbers are the visited cells.
Italicized numbers tell how many exits
remain from the unvisited cells.)

(10)

Four cells are now candidates for step 9, and they’re all currently marked ‘2 ’. So
there’s a four-way tie. In such cases, von Warnsdorf explicitly said that it’s OK
to choose arbitrarily, among all cells that have the fewest exits. Let us therefore
proceed boldly to cell 33 (between 4, 5, and 6). That makes a two-way tie; and
we might as well go next to 41 (just to the right of 7). From here we don’t want
to go to the middle square, which has just dropped from 8 to 7, because our

December 4, 2025

SGB format
linear time
greed
seven deadly sins
morality
virtue

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: A GREEDY HEURISTIC

7

other choice is a 1. And now it’s plain sailing, as von Warnsdorf leads us on a
merry chase — ending gloriously with move 25 in the center cell 22.

It’s easy to implement Warnsdorf’s rule, by representing the given graph in
SGB format. (The reader should be familiar with this format; see, for example,
Algorithm 7B and the remarks that precede it.) The node for each vertex v
in Algorithm W below extends the basic format by including two utility ﬁelds,
DEG(v) and TAG(v), which correspond to the italic and bold numbers in (10).
Algorithm W allows the user to specify “target” vertices t1, . . . , tr, which are
to be visited only when no other vertices are available. A similar mechanism was,
in fact, used by von Warnsdorf himself, in the advanced examples of his original
booklet that introduced the idea [Des R¨osselsprunges einfachste und allgemeinste
L¨osung (Schmalkalden, 1823); see also Schachzeitung 13 (1858), 489–492].

Algorithm W (Warnsdorf ’s rule). Given a graph G, a source vertex s, and op-
tional target vertices t1, . . . , tr, this algorithm applies Warnsdorf’s rule to ﬁnd a
(hopefully Hamiltonian) path v1, v2, . . . that begins with s. Let n = N(G) be the
number of vertices of G; let v0 = VERTICES(G) be G’s initial vertex in memory.
W1. [Initialize.] For 0 ≤ k < n and v ← v0 + k, do the following: Set d ← 0,
a ← ARCS(v); while a (cid:4)= Λ, set d ← d + 1 and a ← NEXT(a); then set
DEG(v) ← d and TAG(v) ← 0. (Thus DEG(v) is the degree of v.) Finally
set k ← 0, v ← s, and DEG(ti) ← DEG(ti) + n for 1 ≤ i ≤ r.

W2. [Visit v.] Set k ← k + 1, vk ← v, TAG(v) ← k, a ← ARCS(v), and θ ← 2n.
W3. [All arcs tested?] If a = Λ, go to W7. Otherwise set u ← TIP(a), and go to
W6 if TAG(u) (cid:4)= 0. (Vertex u is a neighbor of vk and a candidate for vk+1.)

W4. [Decrease DEG(u).] Set t ← DEG(u) − 1 and DEG(u) ← t.
W5. [Is DEG(u) smallest?] If t < θ, set θ ← t and v ← u.
W6. [Loop over arcs.] Set a ← NEXT(a) and return to W3.
W7. [Done?] If θ = 2n, terminate with path v1 . . . vk. Otherwise go to W2.
Notice that the candidates for vk+1 are precisely the vertices u whose DEG needs
to change when vk leaves the active graph. Therefore this algorithm runs in linear
time: Every arc is examined at most twice, once in step W1 and once in step W3.
The path chosen by Algorithm W depends on the ordering of arcs that lead
out of each vertex in SGB format, because Warnsdorf’s rule makes an arbitrary
decision in case of ties. A simple change to step W5 will randomize the path
properly, as if all orderings of the arcs were equally likely (see exercise 53).

Now that we understand Warnsdorf’s rule, let’s talk a little bit about greed.
Greed is of course one of the seven deadly sins; hence we might well question
the morality of ever using a greedy algorithm in our own work. However, greed
is actually a virtue, when it enhances the environment and harms nobody.

In what sense is Algorithm W greedy? From the standpoint of short-term
greed, also known as “instant satisfaction,” the best choice for vk+1 would seem
to be a vertex with maximum degree, not minimum, because that vertex will
give us the most ﬂexibility when choosing vk+2. But from the standpoint of
long-term greed, also known as “risk management” or maximizing our chance

December 4, 2025

de Jaenisch
Hamilton
dodecahedron graph
3-regular
n-cube
Gray binary codes
perms
change ringing
binary
binary trees
rotation
NP-complete
Pohl

8

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

of success, it’s best to choose a vertex with minimum degree, as von Warnsdorf
stipulated; that choice leaves us with the most arcs remaining for moves in the
future. Indeed, short-term greed turns out to be very bad (see exercise 59).

How good is Warnsdorf’s rule? It works so well for knight moves that von
Warnsdorf na¨ıvely believed it to be infallible, except perhaps on m × n boards
with m < 6 or n < 6. He even thought that he had a proof of guaranteed success.
His booklet exhibited many examples: 6×6, 6×7, . . . , up to 10×10. Experiments
by C. F. de Jaenisch [Trait´e des applications de l’analyse math´ematique au jeu
des ´echecs 2 (1862), 59] showed in fact that, on an ordinary 8 × 8 chessboard,
one can basically choose the ﬁrst 40 moves at random, and obtain a complete
knight’s tour by applying Warnsdorf’s rule only to the last 24 steps!

The rule can fail, however. On a 6 × 6 board, it gives a complete tour
about 97.2% of the time, yet it sometimes stops after only 32 or 34 steps if the
starting position is one of the eight interior diagonal squares. On the 8 × 8 board
it succeeds even more often (about 97.9%). Yet with probability 0.0000038 it
might stop with a path of length 39, as shown in the answer to exercise 59.

15
128 ≈ .117. That probability rises to

Hamilton’s dodecahedron graph (Fig. 122) is quite diﬀerent from a graph of
knight moves, because it is 3-regular. A partial path in a 3-regular graph can
be extended in at most two ways, after we’ve selected the ﬁrst two points, while
a knight can have up to seven choices at every step. (Furthermore, all starting
edges of the dodecahedron are equivalent.) Nevertheless, Algorithm W handles
31
that graph well: It ﬁnds a Hamiltonian path v1v2 . . . v20 with probability
32 =
.96875. Furthermore, it ﬁnds a path with v20 −−−v1 (hence a Hamiltonian cycle)
139
with probability
256 ≈ .543 if we set t1 to
a neighbor of s; it’s exactly 1/2 if we set {t1, t2, t3} to the three neighbors of s.
It’s not diﬃcult to see that Algorithm W always works perfectly when G is
the graph of a rectangular grid and s is a corner vertex (see exercise 62). With
a bit more thought, we can even prove that it always succeeds when G is an
n-cube, thereby ﬁnding many examples of the generalized Gray binary codes
that we studied in Section 7.2.1.1 (see exercise 63). When G is the SGB graph
perms(−4, 0, 0, 0, 0, 0, 0) — whose vertices are the permutations of {0, 1, 2, 3, 4},
related by swapping adjacent digits — Warnsdorf’s rule ﬁnds “change ringing”
paths of length 5!−1 = 119 about 29% of the time. (See Algorithm 7.2.1.2P. This
probability drops to less than 2%, however, with permutations of 6 elements, and
to near zero with permutations of 7.) Another instructive example is the SGB
graph binary(10, 0, 0), whose vertices are the 16796 binary trees with 10 nodes,
related by “rotation.” Starting at the tree with all-null left links, Algorithm W
ﬁnds a Hamiltonian path about 5.6% of the time. (See Algorithm 7.2.1.6L.)

Of course Algorithm W isn’t a panacea. We can’t expect any algorithm to
solve the NP-complete Hamiltonian path problem in linear time! Warnsdorf’s
rule certainly has diﬃculty in critical cases; indeed, it can fail spectacularly even
on small graphs (see exercise 65). But it’s often a good ﬁrst thing to try, when
presented with a graph that we haven’t seen before.

Ira Pohl [CACM 10 (1967), 446–449; 11 (1968), 1] has suggested breaking
ties in Warnsdorf’s rule by looking at the sum of the degrees of vk’s neighbors.

December 4, 2025

path ﬂipping–
ﬂipping paths–
path exchange, see path ﬂipping
Euler
Bertrand
breedy
mutations
genetic algorithms
closed

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: PATH FLIPPING

9

Path ﬂipping. Long before Warnsdorf’s time, the great mathematician Leon-
hard Euler had already published a classic paper about knight’s tours [M´emoires
de l’acad´emie des sciences de Berlin 15 (1759), 310–337], in which he showed
how to discover long paths by a completely diﬀerent method. (Euler credited
this idea, at least in part, to his friend Louis Bertrand.) Instead of Warnsdorf’s
“greedy” algorithm, his approach might be called a “breedy” method, because
it proceeded by simple mutations and adaptations of paths already known.

Suppose, for example, that we want to ﬁnd a 3 × 10 knight’s tour, and that

Warnsdorf has already told us how to reach 28 of the 30 cells:

4 7 2 27 24 13 10 19 a 17
1 28 5 14 9 22 25 16 11 20
6 3 8 23 26 15 12 21 18 b

.

(11)

We can’t go from position 28 to an unvisited cell; but we needn’t despair, because
28 is just one knight’s move away from cell 23. Similarly, cell 1 is adjacent to 8.
Therefore we can immediately deduce that two more equally long paths exist:

1 . . 23, 28 . . 24;

7 . . 1, 8 . . 28.

(12)

(Here ‘x . . y’ stands for the path from x to y that proceeds by unit steps ±1.)
Operating in the same fashion on the ﬁrst of these yields three more,

1 . . 5, 24 . . 28, 23 . . 6; 1 . . 15, 24 . . 28, 23 . . 16; 7 . . 1, 8 . . 23, 28 . . 24.

(13)

And, aha, one of these can be extended to a full tour 1 . . 15, 24 . . 28, 23 . . 16, b, a:

4 7 2 19 16 13 10 25 30 27
1 20 5 14 9 22 17 28 11 24
6 3 8 21 18 15 12 23 26 29

.

(14)

Now the same subpath-ﬂipping technique leads from (14) to additional tours

1 . . 17, 30 . . 18;

1 . . 23, 30 . . 24;

7 . . 1, 8 . . 30;

(15)

and we can continue to ﬁnd tours galore:

1 . . 13, 18 . . 30, 17 . . 14;
7 . . 1, 8 . . 23, 30 . . 24;

1 . . 5, 18 . . 30, 17 . . 6;

7 . . 1, 8 . . 17, 30 . . 18;

13 . . 8, 1 . . 7, 14 . . 30;

1 . . 7, 14 . . 17, 30 . . 18, 13 . . 8;

Indeed, the latter is a Hamiltonian cycle — a closed tour — because 1 is
etc.
adjacent to 8! A Hamiltonian cycle represents 30 diﬀerent Hamiltonian paths,
each of which leads to further ﬂips, hence further paths and cycles.

If we start with (14) and keep ﬂipping until no new paths arise, it turns out
that we will have discovered all 16 of the Hamiltonian cycles of the 3 × 10 knight
graph, as well as 2472 of its 2568 noncyclic Hamiltonian paths.

One of the 96 noncyclic Hamiltonian paths not derivable from (14) is

1 12 3 22 15 10 7 26 29 18
4 23 14 11 6 25 20 17 8 27
13 2 5 24 21 16 9 28 19 30

.

(16)

It leads via ﬂips only to three others, namely to 1 . . 17, 30 . . 18; 13 . . 1, 14 . . 30;
13 . . 1, 14 . . 17, 30 . . 18. We wouldn’t have found a cycle, if we’d started with (16).

December 4, 2025

Euler
breadth-ﬁrst search
update
canonical form
breadth-ﬁrst search

10

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

Let’s formulate Euler’s approach more precisely:

Algorithm F (Long paths by ﬂipping). Given a simple path v1 −−− v2 −−−· · · −−−vt
in a connected n-vertex graph, this algorithm repeatedly obtains new paths by
reversing subpaths as explained above, until either exhausting all possibilities or
ﬁnding a path that can be extended by a vertex /∈ {v1, v2, . . . , vt}. An auxiliary
table of vertex labels w[v] is used to discover potential ﬂips.
F1. [Initialize for breadth-ﬁrst search.] Prepare a dictionary, initially empty, for
storing paths of length t − 1. Set w[v] ← 0 for each of the n vertices v of
the graph. Set q ← 0 and perform update(v1, . . . , vt), where update is the
subroutine deﬁned below. Then set d ← p ← p1 ← p2 ← 0 and p0 ← q.

F2. [Done with distance d?]

(At this point we’ve entered q paths into the
dictionary, and we’ve explored the successors of the ﬁrst p paths. Exactly
pi of those paths were obtained by making ≤ d − i ﬂips, for 0 ≤ i ≤ 2.) Go
to F6 if p = p0; otherwise set p ← p + 1.

F3. [Explore path p.] Let u1 −−− u2 −−− · · · −−− ut be the pth path that entered
the dictionary, and set w[uk] ← k for 1 ≤ k ≤ t. Go to F5 if ut −−−u1.
F4. [Process a noncyclic path.] For each vertex v such that ut −−− v, do the
following: Set k ← w[v]; terminate the algorithm if k = 0; otherwise call
update(u1, . . . , uk, ut, . . . , uk+1). Then, for each v such that u1 −−−v, do the
following: Set k ← w[v]; terminate if k = 0; otherwise update(uk−1, . . . , u1,
uk, . . . , ut). Then return to F2.

F5. [Process a cyclic path.]

(A cyclic path will be in the dictionary only if
t = n; see below.) For 1 ≤ j ≤ t and for each v such that uj −−− v,
do the following: Set k ← w[v] (which will be positive). If k < j, call up-
date(uj+1, . . . , ut, u1, . . . , uk, uj, . . . , uk+1) and update(uk−1, . . . , u1, ut, . . . ,
uj, uk, . . . , uj−1); otherwise update(uj+1, . . . , uk, uj, . . . , u1, ut, . . . , uk+1)
and update(uk−1, . . . , uj, uk, . . . , ut, u1, . . . , uj−1). Then return to F2.
F6. [Advance d.] Terminate if p = q (we have found all the reachable paths).
Otherwise set d ← d + 1, p2 ← p1, p1 ← p0, p0 ← q, and go back to F2.
Algorithm F relies on a subroutine ‘update(v1, . . . , vt)’, whose purpose is to put
the path v1 −−− · · · −−− vt into the dictionary unless it’s already there. First the
path is converted to a canonical form, so that equivalent paths are entered only
once: If vt (cid:4)−−− v1, the canonical form is obtained by changing (v1, . . . , vt) ←
(vt, . . . , v1) if v1 > vt. On the other hand if vt −−− v1, the path is cyclic, and we
terminate the algorithm if t < n. (The graph is connected, so there must be a
vertex outside the cycle that is adjacent to a vertex of the cycle.) Finally, if t = n
and vn −−− v1, we obtain the canonical form by permuting the cycle cyclically so
that v1 is the smallest element; then we set (v1, v2, . . . , vn) ← (v1, vn, . . . , v2) if
v2 > vn. Once (v1, . . . , vt) is in canonical form, the update routine looks for it in
the dictionary. If unsuccessful, update sets q ← q+1 and inserts it as the qth path.
The theory of breadth-ﬁrst search tells us that (v1, . . . , vt) cannot match any
path in the dictionary that was obtained with fewer than d − 1 ﬂips. (Otherwise
the path (u1, . . . , ut) that led to it would have been seen before making d ﬂips.)

December 4, 2025

Warnsdorf
permutations
change ringing
all Hamiltonian cycles
all Hamiltonian paths
backtracking
XCC problem
prime queen attacking problem
knight graph

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: SEARCHING FOR ALL

11

Therefore step F6 can save dictionary space and lookup time by deleting all paths
of index ≤ p2 from the dictionary whenever p2 increases. Exercise 73 discusses
a simple trick that makes this deletion painless.

Algorithm F is amazingly versatile. For example, there are 9862 closed
knight’s tours on a 6 × 6 board, and 2963928 open tours. All of them will be
found by Algorithm F, when given any single instance.

We began our search for a 3 × 10 knight’s cycle by using the Warnsdorf-
inspired path (11). But we could have started Algorithm F with t = 1, thus
presenting it with only a single vertex v1. Every time the algorithm ﬁnds a
larger path, we can simply restart it, with t increased.

For example, the author tried the 3 × 10 problem 100 times, choosing v1
at random and ordering the vertex neighbors randomly in steps F4 and F5.
A Hamiltonian cycle was found in 82 cases, usually after making fewer than 100
calls on update. A stubborn Hamiltonian path like (16) was found in 6 cases.
And the remaining 12 cases failed to reach t = 30; once t was even stuck at 22.
Of course that’s a very small problem. When presented with the graph of
permutations of {0, 1, 2, 3, 4, 5}, Algorithm F was able to ﬁnd a “change ringing”
cycle of length 720 in each of ten random trials, averaging less than 50,000
updates per trial. On the other hand it did not do well when trying to ﬁnd a
closed 3 × 100 knight’s tour.

Searching exhaustively. Let’s try now to design an algorithm that systemati-
cally ﬁnds every Hamiltonian cycle of a given graph. Such an algorithm will also
ﬁnd every Hamiltonian path, because exercise 2 shows that every Hamiltonian
path of G corresponds to a Hamiltonian cycle of a related graph G

.

(cid:2)

A Hamiltonian cycle involves every vertex. So we can start it at any
convenient vertex v1. Then there’s an obvious way to grow all possible cycles via
backtracking: For each v2 with v1 −−−v2, we consider each v3 (cid:4)= v1 with v2 −−− v3,
etc. We can also formulate the task as an XCC problem (see, for example, the
“prime queen attacking problem” in Section 7.2.2.3).

But those approaches are overly speciﬁc; there’s usually a much more ef-
ﬁcient way to proceed.
Instead of regarding our task as the assignment of
appropriate labels 1, 2, . . . , n to the n vertices of our graph, it’s better to
regard it as the task of choosing n edges in such a way that (i) every vertex is
an endpoint of precisely two of those edges; (ii) the subgraph deﬁned by those
edges is connected. Indeed, a Hamiltonian cycle is nothing more nor less than an
(unordered) set of n edges that form a single cycle.

Consider, for example, the 3 × 10 knight graph,

, which
has 30 vertices and 50 edges. We can conveniently denote its vertices by two-
digit numbers, {00, 01, . . . , 09, 10, 11, . . . , 19, 20, 21, . . . , 29}, and write its edges
01
compactly in two-line form:
20 , . . . ,

19
27 .

00
12 ,

00
21 ,

17
25 ,

17
29 ,

18
26 ,

Notice that vertices 00, 09, 10, 11, 18, 19, 20, and 29 have degree 2 in this
graph. Consequently the two edges that touch each of them must be present
in any Hamiltonian cycle; in other words, the pattern
is already
forced, before we begin to choose further edges.

December 4, 2025

binary branch: A choice between two possibilitie
outer vertices
inner vertices
bare vertices
sparse-set representation
data structures
invariant relation
adjacency matrix

12

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

04
12 and

00
12 and

05
17 and

02
21 or the edge

In this pattern, vertex 12 belongs to the edges

12
20 , which were forced
from vertices 00 and 20. So 12 already has the two edges that it needs; and the
12
24 , cannot ever be part of a Hamiltonian
other edges that touch it, namely
17
25 .
cycle. We might as well delete them. Similarly, we can delete edges
Nothing else is obviously forced at this point, so we must make a choice. For
13
example, we must use either the edge
21 , because those edges are
the only ways for vertex 21 to reach its quota of two. In other words, our search
tree for the 3 × 10 knight graph must begin with a binary branch.

02
21 . That edge implies in particular that we now have
01 −−− 20 −−− 12 −−− 00 −−− 21 −−− 02 −−− 10 −−− 22 as a subpath of the ﬁnal cycle.
01
13
Consequently edges
21 ,
22
(because it would complete a short cycle!).

02
23 can no longer be used. Nor can the edge

Aha. Only one of the remaining edges touches 01, namely

01
13 . So that
edge is now forced. And then we’re confronted with another two-way branch.
Exercise 108 discusses one sequence of reasonable initial choices, and the reader
is strongly encouraged to study that scenario.

Suppose we choose

02
14 , and

In general, as we’re trying to visit all Hamiltonian cycles of a given graph,
we’ll have a partial solution consisting of a set of disjoint subpaths to be included,
and a set of edges by which those subpaths might be extended until a complete
cycle is obtained. The subpaths are deﬁned by the edges that have been chosen so
far. If there are t subpaths, {u1 . . . v1, . . . , ut . . . vt}, we say that the 2t endpoints
{u1, v1, . . . , ut, vt} are “outer” vertices; any vertex that lies on a subpath but is
not an endpoint is called “inner”; and all other vertices are “bare.” Every vertex
begins bare, and is eventually clothed. If we reach a state where all but two of the
vertices are inner, and if those two outer vertices are adjacent, we can complete
a Hamiltonian cycle. Success!

Algorithm H below ﬁnds Hamiltonian cycles by essentially starting with a
graph G and removing edges until only a cycle remains.
It uses a sparse-set
representation for G, because such structures are an especially attractive way to
maintain the current status of a graph that is continually getting smaller.

The idea is to have two arrays, NBR and ADJ, with one row for each vertex v.
If v has d = DEG(v) neighbors in G, they’re listed (in any order) in the ﬁrst
d columns of NBR[v]. And if NBR[v][k] = u, where 0 ≤ k < d, we have
ADJ[v][u] = k; in other words, there’s an important invariant relation,

NBR[v][ADJ[v][u]] = u,

for 0 ≤ u < n,

(17)

where n is the number of vertices in G. Neighbors can be deleted by moving them
to the right and decreasing d; neighbors can be undeleted by simply increasing d.
Furthermore, if u is not a neighbor of v, ADJ[v][u] has the impossible value ∞;
thus the ADJ array functions also as an adjacency matrix.

The edges u −−−v of G are considered to be pairs of arcs, u −−→v and v −−→ u,
which run in opposite directions. In particular, we always have ADJ[u][v] = ∞
if and only if ADJ[v][u] = ∞. When an edge is deleted, however, we often need
to delete only one of those arcs in the NBR array, because Algorithm H doesn’t
always need to look at both of them.

December 4, 2025

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: SEARCHING FOR ALL

13

Algorithm H represents the vertices of G by the integers 0 to n − 1, as
we’ve seen in (17). Every vertex v has three ﬁelds: its current degree, DEG(v);
its external name, NAME(v), used only to print the answers; and a special ﬁeld
called MATE(v). We have MATE(u) = v and MATE(v) = u when u and v are the
outer vertices at the ends of a current subpath; and we have MATE(v) = −1 if
and only if vertex v is bare. The value of MATE(v) is undeﬁned when v is an
inner vertex, but it must be nonnegative in that case. (See exercise 109.)

An inner vertex is essentially invisible to our algorithm, because we already
know its context in the ﬁnal cycle. We maintain an array VIS to list the visible
vertices — those that are either bare or outer. VIS is a sparse-set representation,
containing a permutation of the vertices, with the invisible ones listed last. The
inverse permutation appears in a companion array called IVIS, so that we have
(18)
⇐⇒
Vertex v is visible if and only if IVIS[v] < S, where S is a global variable. Thus
v is inner if and only if IVIS[v] ≥ S. Here’s how a vertex becomes invisible:

IVIS[v] = k.

VIS[k] = v

degree
DEG(v)
NAME(v)
MATE(v)
outer vertices
bare
inner vertex
sparse-set representation
visible
invisible
makeinner(v)
trigger list
data structures
doubly linked list
LLINK[v]
RLINK[v]
list head
outer vertices
Insertion
deletion

makeinner(v) =

⎧
⎨

Set S ← S − 1, v
set VIS[S] ← v, IVIS[v] ← S,

← VIS[S], k ← IVIS[v];

VIS[k] ← v

, IVIS[v

] ← k.

(cid:2)

(cid:2)

(cid:2)

(19)

⎩

If u is a bare vertex whose degree decreases to 2, Algorithm H can make
signiﬁcant progress, because the two remaining edges that touch u must both be
part of the cycle. Whenever such a u is discovered, we put it into a “trigger list”
called TRIG. A global variable, T, holds the size of the trigger list. This behavior
is implemented by using the following procedure to delete the arc u −−→v:

Set d ← DEG(u) − 1, k ← ADJ[u][v], w ← NBR[u][d].
If MATE(u) < 0 and d = 2, set TRIG[T] ← u, T ← T + 1.
Set NBR[u][d] ← v, NBR[u][k] ← w,
ADJ[u][v] ← d, ADJ[u][w] ← k;

(20)

set DEG(u) ← d.

remarc(u, v) = ⎧
⎪⎪⎪⎨
⎪⎪⎪⎩

One might think that we’ve now deﬁned a comprehensive set of data struc-
tures for implementing Algorithm H; but we aren’t done yet. There’s also a
doubly linked list, maintained in arrays LLINK[v] and RLINK[v] for 0 ≤ v ≤ n,
with entries LLINK[n] and RLINK[n] serving as the list head. This list contains
all of the current “outer” vertices. More precisely, suppose that there are t
subpaths, and suppose that we have RLINK[n] = v1, RLINK[vj] = vj+1 for
1 ≤ j < 2t, and RLINK[v2t] = n. Then the outer vertices are {v1, v2, . . . , v2t};
and we also have LLINK[n] = v2t, LLINK[vj] = vj−1 for 1 < j ≤ 2t, and
LLINK[v1] = n. Insertion and deletion are accomplished in the usual way:

Set k ← LLINK[n],

LLINK[n] ← RLINK[k] ← v,
LLINK[v] ← k, RLINK[v] ← n.
Set j ← LLINK[v], k ← RLINK[v],
LLINK[k] ← j, RLINK[j] ← k;

makeinner(v).

activate(v) =

deactivate(v) =

December 4, 2025

(cid:5)

⎧
⎨

⎩

(21)

(22)

stack with holes
n-cycle

14

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

The algorithm makes frequent use of the following subroutine:

makemates(u, w) =

If ADJ[w][u] < DEG(w),

remarc(u, w) and remarc(w, u);
set MATE(u) ← w and MATE(w) ← u.

(cid:5)

(23)

Vertices u and w are becoming endpoints. It removes the edge between u and w,
if present, in order to prevent the formation of a short (non-Hamiltonian) cycle.
The current state at each level of the search tree is kept in two sequential
stacks. ACTIVE is an array that remembers which vertices are outer; SAVE is an
array that remembers the mates and degrees of the visible vertices. The SAVE
stack is somewhat unusual because it’s a “stack with holes”: n slots are allocated
to it at every level, but only the slots for visible vertices are actually used.

Level l of the search can in fact involve up to seven state variables: CV(l) is
the outer vertex on which we’re branching; I(l) identiﬁes the neighbor of that
vertex in the currently chosen edge; D(l) is the current degree of CV(l); E(l)
is the number of edges chosen so far; S(l) is the number of vertices that are
currently visible; T(l) and A(l) are the current sizes of TRIG and ACTIVE.

Algorithm H (All Hamiltonian cycles). Given a graph G on the n vertices
{0, 1, . . . , n − 1}, this algorithm uses the data structures discussed above to visit
every subset of n edges that form an n-cycle. During every visit, the chosen
edges are EU[k]−−−EV[k] for 0 ≤ k < n.

H1. [Initialize.] Set up the NBR and ADJ arrays as described in (17). Set the
global variables a ← e ← i ← l ← T ← 0. Also set VIS[v] ← IVIS[v] ← v
and MATE(v) ← −1 for 0 ≤ v < n. Set LLINK[n] ← RLINK[n] ← S ← n.
Finally, for every vertex v with DEG(v) = 2, set TRIG[T] ← v and T ← T+1.

H2. [Choose the root vertex.] Let CURV be a vertex of minimum degree, and set
d ← DEG(CURV) − 1. If d < 1, terminate (there is no Hamiltonian cycle).
If d = 1, set CURV ← −1 and go to H4.

H3. [Force a root edge.] Set CURU ← NBR[CURV][d − i] (the last yet-untried
neighbor of CURV), and set EU[0] ← CURU, EV[0] ← CURV, e ← 1. Then
activate(CURU), activate(CURV), and makemates(CURU, CURV).

H4. [Record the state.] Set CV(l) ← CURV, I(l) ← i, D(l) ← d, E(l) ← e,
S(l) ← S, T(l) ← T. For 0 ≤ k < S, set u ← VIS[k] and SAVE[nl + u] ←
(thereby leaving “holes” in the SAVE stack). Then set
MATE(u), DEG(u)
u ← RLINK[n]; while u (cid:4)= n, set ACTIVE[a] ← u, a ← a+1, u ← RLINK[u].
(cid:6)
Finally set A(l) ← a, and go to H6 if l = 0.

(cid:7)

H5. [Choose an edge.] Set CURU ← NBR[CURV][i], CURT ← MATE(CURU), CURW ←
MATE(CURV), EU[e] ← CURU, and e ← e + 1. If CURT < 0 (CURU is bare),
makemates(CURU, CURW), activate(CURU), and go to H6. Otherwise (CURU is
outer), makemates(CURT, CURW). Call remarc
for k
decreasing from DEG(CURU) − 1 to 0. Then deactivate(CURU).

NBR[CURU][k], CURU

(cid:6)

(cid:7)

H6. [Begin trigger loop.] Set j ← 0 if l = 0, else j ← T(l−1). Go to H10 if j = T.

December 4, 2025

data structures

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: SEARCHING FOR ALL

15

H7. [Clothe TRIG[j].] Set v ← TRIG[j], and go to H9 if MATE(v) ≥ 0 (v is
no longer bare). Otherwise go to H15 if DEG(v) < 2 (Hamiltonian cycle is
impossible). Set u ← NBR[v][0] and v ← NBR[v][1]. Go to H15 if w =
MATE(u) and e (cid:4)= n−2 (cycle is too short). Set EU[e] ← u, EV[e] ← v, e ←
e + 1, EU[e] ← v, EV[e] ← w, e ← e + 1, MATE(v) ← v, and makeinner(v).

H8. [Take stock.] (We’ve just joined v to its only two neighbors, u and w, which
aren’t mates unless e = n.) Update the data structures as described in ex-
ercise 112, based on whether MATE(u)<0 and/or MATE(w)<0 (four cases).

H9. [End trigger loop?] Set j ← j + 1, and return to H7 if j < T.

H10. [Enter new level.] Set l ← l + 1, and go to H13 if e ≥ n − 1.

H11. [Choose vertex for branching.] Set CURV ← RLINK[n], d ← DEG(CURV),
k ← RLINK[CURV]. While k (cid:4)= n, if DEG(k) < d reset CURV ← k and
d ← DEG(k); set k ← RLINK[k]. Go to H14 if d = 0. Otherwise set
EV[e] ← CURV and T ← T(l − 1). (See exercise 129.)

H12. [Make CURV inner.] Call remarc

for 0 ≤ k < d
(thereby removing CURV from its neighbors’ lists). Then deactivate(CURV),
set i ← 0, and go to H4.

NBR[CURV][k], CURV

(cid:6)

(cid:7)

H13. [Visit a solution.] If e < n, set u ← LLINK[n] and v ← RLINK[n]; go
to H14 if ADJ[u][v] = ∞; otherwise set EU[e] ← u, EV[e] ← v, e ← n.
Now visit the n-cycle deﬁned by arrays EU and EV. (See exercise 113.)

H14. [Back up.] Terminate if l = 0. Otherwise set l ← l − 1.

H15. [Undo changes.] Set d ← D(l) and i ← I(l) + 1. Go to H14 if i ≥ d.
Otherwise set I(l) ← i, e ← E(l), k ← (l > 0? A(l − 1): 0), a ← A(l),
v ← n. While k < a, set u ← ACTIVE[k], RLINK[v] ← u, LLINK[u] ← v,
v ← u, k ← k + 1. Then set RLINK[v] ← n, LLINK[n] ← v, S ← S(l),
T ← T(l). For 0 ≤ k < S, set u ← VIS[k] and
←
SAVE[nl + u]. Finally set CURV ← CV(l). Go to H5 if l > 0.

MATE(u), DEG(u)

(cid:6)

(cid:7)

H16. [Advance at root level.] Terminate if CURV < 0. Otherwise set CURU ←
MATE(CURV). (The previous edge CURU−−− CURV is gone.) Set LLINK[n] ←
RLINK[n] ← n, a ← 0, MATE(CURU) ← MATE(CURV) ← −1, S ← n.
(Everything is again bare.) If DEG(CURU) = 2, set TRIG[0] ← CURU and
T ← 1; otherwise set T ← 0. If DEG(CURV) = 2, set TRIG[T] ← CURV and
T ← T + 1. Go to H3 if T = 0. Otherwise set CV(0) ← −1, A(0) ← e ← 0,
and go to H6.

This marvelous algorithm has lots of steps, but it isn’t terribly hard to un-
derstand. Its length arises mostly from the fact that a variety of data structures
need to work together, combined with the fact that special provisions must be
made at root level when no vertex has degree 2. In such cases, which are handled
in steps H3 and H16, we choose a root vertex of minimum degree, and a root
edge that touches it. We ﬁnd all Hamiltonian cycles for which the root edge is
present; then we discard that edge, and repeat the process. Eventually we will
see a vertex of degree 2.

December 4, 2025

16

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

Table 1
A BAKER’S BAKER’S DOZEN OF EXAMPLE GRAPHS FOR ALGORITHM H

Hamiltonian
cycles

Running
time (mems)

Graph

binary trees

Description Vertices Edges Degrees
min . . max
3 . . 19
4 . . 4
3 . . 3
7 . . 22
4 . . 4
3 . . 14
2 . . 6
3 . . 11
2 . . 4
5 . . 5
2 . . 6
3 . . 6
9 . . 11
2 . . 48

A Anna Karenina
B
C concentric rings
D
E
F
G
H
P
Q
R
S Sierpi´nski simplex
T
U

disconnected
expander
Fleischner G3
giraﬀe tours
Halin from π
parity clash
5-cube
“random”

138
84
216
118
96
126
192
227
145
80
125
96
74
154

49
42
144
23
48
57
100
128
82
32
64
34
15
50

tripartite K4,5,6
USA from ME

49152
14306485
66770562
0
107921396
2
4515918298
10128654600
0
906545760
9011601
1165688832
207360000
68656026

Mems per
solution
8429.1
610.8
524.4

414M
8739M
35G
65G
70G

2723M 1.4
3232G
2913G
203G
248G
7087M
310G
40G
181G

∞
648.3
9
10
·
715.6
287.6

∞
273.5
786.4
265.6
190.7
2641.5

tripartite graph, complete
benchmarks+
unstructured
Tolstoy
book
Stanford GraphBase
SGB
4-regular graph
regular graph
binary
binary trees
dodecahedron
concentric rings
Hamilton
components
tough
SGB
raman
Ramanujan graph
expander graph, see raman

One good way to start learning Algorithm H is to play through the steps by

hand when G is a small graph like K3 or K4 or C4. (See exercise 115.)

Algorithm H promises to produce interesting results galore, because the
number of interesting graphs is enormous. We can get an idea of its performance
in practice by studying the statistics of the benchmarks in Table 1, which reports
on many diﬀerent kinds of graphs. Each graph has been given an identifying
letter for convenience.

• A, an “unstructured” graph based on Tolstoy’s novel Anna Karenina. More
precisely, this smallish graph arises from book ("anna", 0, 6, 0, 0, 1, 1, 0) in the
Stanford GraphBase (SGB) after repeatedly removing vertices whose degree is
less than 3. Algorithm H ﬁnds its Hamiltonian cycles in a ﬂash.

• B, by contrast, is a 4-regular graph with a strict mathematical structure. It’s
the SGB graph binary(5, 5, 0), which consists of the binary trees with 5 internal
(Algorithm
nodes; they’re related by the “rotation” operation, 7.2.1.6–(12).
7.2.1.6L deﬁnes a Hamiltonian path in this graph, not a cycle.)

• C is one of the generalized dodecahedron graphs considered in exercise 11,
with parameter q = 36 where Hamilton’s original graph had q = 5.

• D is a contrived example that’s obtained from six disjoint copies of K3,
together with a copy of K5 whose ﬁve vertices are joined to everything else.
It has no Hamiltonian cycles, because it breaks into six nonempty components
when the ﬁve vertices of K5 are removed. (In the terminology of exercise 117,
graph D isn’t “tough.” Every Hamiltonian graph is tough.)

• E is the SGB graph raman(3, 47, 1, 1), a “Ramanujan graph of type 1.” The
vertices are {0, 1, . . . , 46, ∞}, and the edges are described in exercise 119.

December 4, 2025

-rotational symmetry

Fleischner
unique Hamiltonian cycle
giraﬀe
knight
leaper
◦
90
Kra¨ıtchik
Cossack cross
cross
Halin graphs
grid graph
bipartite graph
5-cube
Gray cycles
random
gunion
random graph
board
Sierpi´nski tetrahedron
unstructured
ZDD

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: SEARCHING FOR ALL

17

• F is a minor of the amazing 338-vertex graph introduced by H. Fleischner in
2013. His graph has 318 vertices of degree 4, 20 vertices of degree 14, and exactly
one Hamiltonian cycle(!). (See exercise 120.)

• G is a graph of 10 × 10 “giraﬀe” moves, where a giraﬀe is like a knight in
chess except that it’s a (4, 1)-leaper instead of a (2, 1)-leaper.
◦
For example, the attractive tour shown here, which has 90
-
rotational symmetry, was published by Maurice Kra¨ıtchik in
§67 of his pioneering book Le Probl`eme du Cavalier (Paris:
Gauthiers[sic]-Villars, 1927). Graph G requires the giraﬀe to
make a special kind of tour whose diagram exhibits a “Cossack
cross” in the four central squares. (A symmetrical example of
such a tour appears in the answer to exercise 149.)

• H is a representative example of a large family of planar Hamiltonian graphs
called “Halin graphs.” (See exercises 122–125.)

• P is a non-Hamiltonian graph that’s another kind of Achilles heel for Algo-
rithm H. We obtain it by appending new vertices ‘!’ and ‘!!’ to the 8 × 10 grid
graph P8
P10, with three new edges u −−− ! −−− !! −−− v, where u and v are
opposite corners of the grid. There’s no Hamiltonian cycle; for if we collapse ‘!’
with 41
and ‘!!’ into a single vertex, we obtain an equivalent bipartite graph P
vertices in one part and 40 vertices in the other. Unfortunately, Algorithm H
doesn’t understand this. So it explores zillions of fruitless paths.

(cid:2)

• Q is the familiar 5-cube, P2 P2 P2 P2 P2, whose Hamiltonian cycles are
the 5-bit “Gray cycles” that we investigated in Section 7.2.1.1.

Their total number, about 900 million, is just half of the value of d(5) that
was reported in Eq. 7.2.1.1–(26). Hmmm; was that a mistake? No: d(5) considers
the cycles (v0 . . . v31) and (v31 . . . v0) to be diﬀerent, while Algorithm H does not.

• R is a graph obtained by adding 64 “random” edges to a 64-cycle. More
precisely, it’s the SGB graph whose oﬃcial name is

gunion(random graph(64, 64, 0, 0, 0, 0, 0, 1, 1, 3142), board(64, 0, 0, 0, 1, 1, 0), 0, 0).

It has only 125 edges, because three of the added edges were already present.
(4)
3 , which was deﬁned and illustrated in

• S is the Sierpi´nski tetrahedron S
Section 7.2.2.3 (Fig. 114). Lots and lots of Hamiltonian cycles here.

• T is a special case of exercise 106.

• U, the graph that’s last but not least in Table 1, is another unstructured
example from “real life.” It revisits the graph of the 48 contiguous states of the
USA, 7.1.4–(133), augmented by two additional vertices ‘!’ and ‘!!’; there are
edges !! −−−ME, and ! −−−v for all v /∈ {ME, !}. Thus its Hamiltonian cycles are the
same as the Hamiltonian paths in 7.1.4–(133) from ME to any other state. (We
used ZDD technology to treat those 68 million paths in Section 7.1.4.)

December 4, 2025

census
knight’s tours–
author
McKay
closed knight’s tours
rotation–
reﬂection–
equivalence classes
bunches
wedge
al-‘Adl¯ı

18

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

A census of knight’s tours. Soon after the author had ﬁrst learned to program
a computer in the 1950s, he wondered whether he’d be able to list all of the
closed knight’s tours on a chessboard. Alas, however, he quickly learned that
the number of such tours is humongous — way too large to be computed by the
slow machines of those days. So his hopes were dashed. In fact, nobody even
had a good estimate for the total number of possibilities, until forty years later.
That ancient riddle was ﬁnally solved, hurray, by Brendan D. McKay, who
proved (without actually constructing them) that the total number of closed
[Technical Report TR-CS-97-03
knight’s tours is exactly 13,267,364,410,532.
(Computer Science Department, Australian National University, 1997), 4 pages.]
Hmmm. Thirteen trillion is indeed a huge number. Yet it isn’t completely
out of reach. If we can visit one tour every microsecond, we can visit them all
in 13 million seconds, which is about 5 months. Also, if we represent each tour
as a 168-bit vector that shows which edges are used, we can store all the tours
in about 279 terabytes; and we’ll see later that further compression is possible.
Furthermore, the vast majority of knight’s tours belong to sets of eight
that are essentially the same, except for rotation and/or reﬂection of the board.
Indeed, McKay found that there are 1,658,420,247,200 equivalence classes of
size 8, and 608,233 equivalence classes of size 4 (see exercise 137); hence the
total number of essentially diﬀerent closed tours is the sum of those two numbers,
namely 1,658,420,855,433. We could ﬁt them all into at most 35 terabytes.

Instead of storing them all, however, we can actually compute them all, in
a fairly short time, if we exploit parallelism. The idea is to partition the set
of all tours into a large number of bunches, where the members of each bunch
can be computed rapidly by Algorithm H. Every bunch is independent of the
others. Therefore several bunches can be computed simultaneously, if we have a
computer that has several processing units.

8
2

Suppose C is a closed knight’s tour. Let’s say that the wedge of C at cell
(i, j) is the pair of edges that touch that cell in C. At most 8 edges touch any cell;
hence there are at most
= 28 possible wedges at any cell, and it’s convenient
to give each of those possibilities a code letter, as shown in Fig. 123.

(cid:6)
(cid:7)
4
We shall partition the closed tours into 28

bunches, based on their wedges
at the four central cells. More precisely, we shall number the rows and columns
from top to bottom and left to right with the digits 0 to 7, and we shall place each
tour into the bunch that corresponds to its wedges at cells 33, 34, 43, and 44.

A slightly tricky rule turns out to be a good way to give a four-letter name
to every bunch, by writing down the code letter for the wedge at 34 after rotating
◦
◦
the tour clockwise by 0
, respectively. For example, let’s
, and 270
look again at al-‘Adl¯ı’s historic tour (1); it clearly has wedge c at cell 34. Rotating
◦
clockwise puts cell 33 into position 34, where we now see wedge z. Another
it 90
◦
rotation yields wedge b at 34 (because B was originally at 43). And a ﬁnal
90
rotation gives us another z. Therefore cycle (1) belongs to bunch czbz.

◦
, 180

, 90

◦

Notice that the four equivalent tours obtained from (1) by rotation belong to
bunches czbz, zbzc, bzcz, and zczb. In general, the tours of bunch α1α2α3α4

December 4, 2025

top-bottom reﬂection
multiplicity
canonical
ASCII
uppercase letters

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: A KNIGHT’S CENSUS

19

a

b

A

B

c

d

C

D

e

f

E

F

g

h

G

H

i

j

I

J

k

l

K

L

w

x

y

z

}

3
4

≈

−

θ = arctan

,
{
}
c, d, C, D
are slightly wider,
{
53◦. Eight wedges, namely
≈
, make a 90◦ turn. Then come
,

Fig. 123. The 28 possible wedges of a knight.
a, b, A, B
The angle θ of the narrowest wedges,
37◦;
is arctan
4
90◦
3
e, f, E, F, g, h, G, H
{
k, l, K, L
i, j, I, J
}
{
at 180◦
w, x, y, z
}
are straight. Notice that a 90◦ counterclockwise
rotation changes a
k; w
L
l

127◦; and
143◦. Finally, wedges

, at 90◦ + θ
θ

a; . . . ; k
x.

A
(cid:4)→
w; and x

}
−

{
{

b
y

(cid:4)→

(cid:4)→

≈

≈

B

K

z

}

(cid:4)→
(cid:4)→

(cid:4)→
(cid:4)→

(cid:4)→

(cid:4)→

(cid:4)→

(cid:4)→

(cid:4)→

are equivalent to the tours of bunches α2α3α4α1, α3α4α1α2, and α4α1α2α3
whenever each αj is one of the 28 wedge codes.

Reﬂection also gives an equivalent tour, whose bunch depends only on the
unreﬂected bunch name. For example, the top-bottom reﬂection of cycle (1) gives
a cycle that belongs to bunch yByD. In general, let ρ and τ be the permutations
◦
of wedge codes that correspond to 90
rotation and to top-bottom reﬂection.
Then α (cid:12)→ αρ is the mapping discussed in Fig. 123, and we have

α = a b c d e f g h i j k l A B C D E F G H I J K L w x y z ;
αρ = b A d C f E h G j I l K B a D c F e H g J i L k y z w x ;
ατ = B A C d G h E f I j l k b a c D g H e F i J L K z y x w ;
¯α = ατ ρ = a B D C H G F E J I K l A b d c h g f e j i k L x w z y .

(24)

Exercise 142 shows that top-bottom reﬂection maps α1α2α3α4 (cid:12)→ ¯α4 ¯α3 ¯α2 ¯α1.

4
The main consequence is that, if α1α2α3α4 is any one of the 28

bunches,

its closed tours are equivalent to those of seven other bunches:

α2α3α4α1, α3α4α1α2, α4α1α2α3, ¯α4 ¯α3 ¯α2 ¯α1, ¯α3 ¯α2 ¯α1 ¯α4, ¯α2 ¯α1 ¯α4 ¯α3, ¯α1 ¯α4 ¯α3 ¯α2. (25)

In most cases these eight bunches are distinct, and we say that α1α2α3α4 has
multiplicity 8. For example, the equivalent bunches czbz, zbzc, bzcz, zczb,
yByD, ByDy, yDyB, DyBy all have multiplicity 8. But sometimes all eight bunches
are identical, and we say that the multiplicity is 1. (There are just four bunches
of multiplicity 1, namely aaaa, llll, AAAA, and LLLL.) Exercise 146 shows that
30 canonical bunches have multiplicity 2; and 774 of the canonical bunches have
multiplicity 4. The multiplicity is always equal to either 1 or 2 or 4 or 8.

A bunch is canonical if it is the lexicographically smallest of the bunches
equivalent to it, where the lexicographic order uses ASCII code (so that upper-
case letters precede lowercase letters). For example, ByDy is canonical;
it’s
lexicographically smaller than bzcz and the other six equivalent bunches.

Although there are 28

= 614656 bunches altogether, only 77245 of them are
canonical. Furthermore, no knight’s tour has ‘a’ anywhere in its bunch name; do
you see why? This reduces the number of relevant canonical bunches to 66771.
(See exercises 145 and 148.)

4

December 4, 2025

symmetry
parallelism
diverse knight’s tours+

20

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

In order to carry out a census of all the closed knight’s tours, it there-
fore suﬃces to solve subproblems of the form “Visit all of the tours in bunch
α1α2α3α4,” for 66,771 canonical names α1α2α3α4. And each of those 66,771
subproblems asks for the Hamiltonian cycles on a modiﬁed 8 × 8 knight graph,
where eight particular edges are forced to be part of the cycle. Equivalently, 24
particular edges of that knight graph are forbidden. Every subproblem is in fact
“Algorithm H friendly,” because at least 16 of the remaining edges — 8 edges in
the center, and 8 edges in the corners — are forced.

For instance, it turns out that bunch ByDy has exactly 31,905,973 tours; and
Algorithm H needs only 16 Gμ (a few seconds) to visit them all. The same is
true, of course, for bunch czbz; but we don’t need that bunch in our census,
because it’s not canonical.

One easy way to carry out the census is to prepare ten shell scripts, each
with 6677 or 6678 of the subproblems. Then run all the scripts simultaneously,
on a machine with 10 processors. At the time this section was written, the
job was thereby accomplished with oﬀ-the-shelf hardware in less than two days.
Notice that this strategy, via bunches, saves a factor of 8 because of symmetry,
and another factor of 10 because of parallelism.

Almost all of the 66,771 bunches contributed solutions; the only exceptions
were 198 cases of the form αlβl or lαlβ, and Algorithm H rejected them
immediately. The smallest nonempty canonical bunch class was CFgd, with only
165,504 solutions (80 Mμ); the largest was LLLL, with 652,228,612 solutions
(287 Gμ); the median was Cflz, with 17,440,101 solutions (8587 Mμ). To get
the total number of tours, we simply compute the sum, over all bunches, of the
number of solutions times the multiplicity. (Without multiplying by multiplicity,
the total number of solutions over all bunches came to 1,671,517,634,718.)

The scheme just described has worked well, but we could have conducted
the census in many other ways. For example, instead of deﬁning bunches based
4
on the 28
possible wedges at the four central cells, we could have based our
8
possible wedges at centrally located boundary cells. Or we
deﬁnition on the 6
8
could have used the 5
possible wedges at the cells that are a knight’s move away
from a corner. Exercises 151 and 152 explore those interesting alternatives.

The ability to conduct a reasonably quick census opens the door to the
solution of many problems that were long thought to be out of reach, and it also
raises new questions that are interesting in their own right. For example, how
many of the 13 trillion possible tours involve each of the 28 possible wedges at
least once? (Answer: 278,078,503,988.) How many of those tours involve each
wedge at least twice? (Answer: 155,528.) And how many of those doubly diverse
tours involve each wedge at most thrice? (Answer: 70,240.) In the latter tours,
exactly eight of the 28 wedges occur three times, because 64 = 20 · 2 + 8 · 3.

It turns out that Algorithm H is not the bottleneck when answering ques-
tions of this kind: The process of analyzing a tour tends to take longer than the
process of generating the tour itself, because Algorithm H is so eﬃcient. The
total time is therefore roughly equal to the time to analyze 1.67 trillion tours,
divided by the degree of parallelism.

December 4, 2025

7.2.2.4 HAMILTONIAN PATHS AND CYCLES: DYNAMIC ENUMERATION

21

Exercises 156–164 are devoted to a wide variety of questions that can be
answered by a good census-taker, and Fig. A–19 in the answer pages is a gallery
of knight’s tours with unusual properties. For example, one of the 70,240 tours
with maximally diverse wedges appears in Fig. A–19(a).

What’s the maximum number of times that a knight can make the sharpest
◦
?
possible turn during a complete cycle, forming a tight angle of just θ ≈ 37
(See Fig. 123.) Contrariwise, what’s the maximum number of times that it can
continue in the same direction as its previous move, making no turn at all?
Exercise 158 clears up those riddles.

topological type
dynamic enumeration–
induced subgraph
Hamilton
dodecahedron

I

II

III

IV

V

VI

VII

VIII

IX

X

XI

XII

XIII

Fig. 124. The thirteen topological types of knight’s cycles.

Every Hamiltonian cycle on an n
n knight graph includes eight ﬁxed edges,
forming narrow wedges at each corner. The endpoints of those wedges
can be connected up in 13 essentially diﬀerent ways, modulo rotation and
reﬂection, indicated by dashed lines in these diagrams. (The actual paths
of interconnection can, of course, have wildly diﬀering lengths and shapes.)

×

Figure 124 suggests a census-oriented question of a diﬀerent kind, because it
points out that there are 13 fundamentally diﬀerent kinds of knight’s cycles on a
square board. How many tours are of each topological type? (See exercise 156.)

Dynamic enumeration. Let’s switch gears now and focus on counting. Instead
of trying to visit every Hamiltonian cycle of a given graph, we’ll try only to ﬁgure
out exactly how many such cycles exist.

Algorithm E below is, in fact, designed to solve a somewhat more general
problem: Given a graph G on the vertices {1, 2, . . . , n}, we’ll determine the
number of m-cycles in the induced subgraph Gm = G | {1, . . . , m}, for 3 ≤ m ≤ n.
In particular, when m = n we’ll know the number of Hamiltonian cycles in G.

Algorithm E is easy to understand, once you understand it, but not so easy to
explain. We shall study it by looking ﬁrst at how it applies to Hamilton’s original
example, the vertices of a dodecahedron. To start, let’s redraw Fig. 122(a) so
that the vertices are named {1, 2, . . . , 20}:

1

1

1

17

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

;

15

13

17

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

;

15

13

17

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

.

(26)

15

13

On the left is Hamilton’s graph G; in the middle is an 8-cycle in G8, clearly
unique; on the right is the 20-cycle of Fig. 122(b).

December 4, 2025

22

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

The key idea that underlies Algorithm E is the notion of an “m-conﬁg,”
which is a subset of the edges that satisﬁes three properties: (i) Every vertex
≤ m appears in exactly two edges.
(ii) No edge has both endpoints > m.
(iii) There is no cycle of edges. One consequence of (i) and (iii) is that the edges
of an m-conﬁg always form disjoint subpaths of the graph. One consequence
of (ii) is that the only 0-conﬁg is the empty set.

m-conﬁg
m-frontier
outer
inner
bare
m-class

For example, Hamilton’s graph obviously has just ﬁve 2-conﬁgs, namely

1

1

1

1

1

17

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

5

7

9

;

(27)

15

13

and they contain respectively 1, 1, 1, 1, 2 subpaths.

The “m-frontier” Fm of G is the set of vertices > m that are reachable from
{1, . . . , m}. Building on our experience with Algorithm H, we classify each vertex
of Fm in an m-conﬁg as either “outer” (an endpoint of a subpath), or “inner”
(an intermediate vertex of a subpath), or “bare” (not in any subpath), according
as its degree in the m-conﬁg is 1, 2, or 0. (There’ll be exactly 2t outer cells when
there are t subpaths.) Two m-conﬁgs are equivalent if they have the same outer,
inner, and bare cells, and if the outer cells are paired up in the same way.

F2 = {3, 5, 17, 19}, and no two of the 2-conﬁgs in (27) are equivalent. But
when m gets larger, we usually have fairly large equivalence classes. For instance,
it turns out that Hamilton’s graph has exactly 32 16-conﬁgs, including these ﬁve:

1

1

1

1

1

17

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

;

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

5

7

9

.

(28)

15

13

The ﬁrst three of these are equivalent, and so are the last two. Furthermore,
every 16-conﬁg turns out to be equivalent either to one of those or to one of

1

1

1

1

17

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

,

15

13

19

18

2

20
16

4
8

12

14

10

11

3

6

7

9

5

17

, or

15

13

19

18

2

20
16

4
8

12

14

10

11

5

.

3

6

7

9

(29)

15

13

Algorithm E works by systematically discovering every “m-class,” namely,
each equivalence class of m-conﬁgs, while also computing all of the class sizes. So
it’s important to give an appropriate name to each m-class. When Fm has q ele-
ments (u1, . . . , uq), this name consists of q integers aj, one for each element of the
frontier: If uj is inner, aj is −1 (written ‘¯1’ for short). If uj is bare, aj = 0. And if
uj is outer, with mate uj
> j, we set aj and
aj
to the smallest positive integer not assigned to an outer vertex ui with i < j.
For example, the frontier F16 is (u1, u2, u3, u4) = (17, 18, 19, 20). The 16-
class at the left of (28) has a subpath from 18 to 20, with 17 inner and 19 bare;
so its name is ¯1101. The class at the right has a subpath from 18 to 19 and
leaves both 17 and 20 bare; so its name is 0110. The names of the four classes

at the other end of its subpath and j

(cid:2)

(cid:0)

(cid:0)

December 4, 2025

7.2.2.4 HAMILTONIAN PATHS AND CYCLES: DYNAMIC ENUMERATION

23

in (29) are respectively ¯111¯1, 1001, 101¯1, and 1212. (Check them!) Algorithm E
determines not only that every 16-conﬁg belongs to one of those six classes, but
also that the classes contain respectively 4, 2, 6, 6, 4, and 10 conﬁgs.

full disclosure
extended frontier
notation (cid:12)→m

Confession: The statements above are almost true, but not really correct.
Algorithm E actually works with an extended frontier
Fm = Fm ∪ {m + 1},
instead of with Fm, for 0 ≤ m < n; in particular,
F0 = {1}. This modiﬁcation
makes the program simpler. And it doesn’t change the deﬁnition of equivalence
classes, because vertex m + 1 will always be bare if it wasn’t already in Fm.

(cid:8)

(cid:8)

The precise ordering of vertices (u1, . . . , uq), where q = |

Fm|, is important
for naming the m-classes. A somewhat peculiar rule turns out to work best: We
−
−
m =
divide
m ;
−
m ﬁrst, otherwise sorting into increasing order:
F
then we place the elements of
(cid:8)
−
m , {uq0+1, . . . , uq} =

(cid:7)
(cid:8)
+
m, where q0 = |

Fm into two parts,

Fm−1 ∪ {m+1}

{u1, . . . , uq0} =

F
\ {m} and
(cid:8)

+
m =

Fm \

−
m |;

F

F

F

F

F

(cid:8)

(cid:8)

(cid:8)

(cid:6)

(cid:8)
(30)

(cid:8)

(cid:8)

uj < uj+1 for 1 ≤ j < q and j (cid:4)= q0.

(cid:8)

(cid:8)

For example, the extended-and-ordered frontiers of Hamilton’s graph are

F0 = (1);
F1 = (2, 5, 17);
(cid:7)
F2 = (3, 5, 17, 19);
(cid:7)
F3 = (4, 5, 17, 19, 6);
(cid:7)
F4 = (5, 6, 17, 19, 8, 20);
(cid:7)
F5 = (6, 8, 17, 19, 20, 9);
(cid:7)
F6 = (7, 8, 9, 17, 19, 20);
(cid:7)
(cid:7)
Notice that

F7 = (8, 9, 17, 19, 20, 10);
F8 = (9, 10, 17, 19, 20, 12);
(cid:7)
F9 = (10, 12, 17, 19, 20, 13);
(cid:7)
F10 = (11, 12, 13, 17, 19, 20);
(cid:7)
F11 = (12, 13, 17, 19, 20, 14);
(cid:7)
F12 = (13, 14, 17, 19, 20, 16);
(cid:7)
F13 = (14, 16, 17, 19, 20);
(cid:7)
(cid:7)

Fm always begins with u1 = m + 1.

F14 = (15, 16, 17, 19, 20);
F15 = (16, 17, 19, 20, 18);
(cid:7)
F16 = (17, 18, 19, 20);
(cid:7)
F17 = (18, 19, 20);
(cid:7)
F18 = (19, 20);
(cid:7)
F19 = (20).
(cid:7)
(cid:7)

(31)

(cid:8)

Everything works nicely because we can readily enumerate all the m-classes
once we know the names and sizes of all the (m−1)-classes. Indeed, the transition
from m − 1 to m means that vertex m gains respectively (0, 2, 1) neighbors if it
is (inner, bare, outer). And the state of vertex m in an (m−1)-conﬁg is the ﬁrst
digit of its class name; thus vertex m gains (0, 2, 1) neighbors if and only if that
name begins with (¯1, 0, 1), respectively.

When m = 17, for example, we know that Hamilton’s 16-conﬁgs have the
class names ¯1101, ¯111¯1, 0110, 1001, 101¯1, 1212. In cases ¯1101 and ¯111¯1, vertex 17
is already inner; so those cases are already 17-conﬁgs. In case 0110, the class
ﬁzzles out and leads to no 17-conﬁgs, because vertex 17 has only one neighbor
in the frontier (namely vertex 18) and it cannot gain two. Cases 1001, 101¯1 and
1212 do lead to 17-conﬁgs, when 17 is joined to 18; see exercise 173.

Let’s write ‘α (cid:12)→m β’ if the (m−1)-class α can lead to the m-class β. Then

we can verify, using (31), that the sequence

0 (cid:12)→1 011 (cid:12)→2 1221 (cid:12)→3 01122 (cid:12)→4 121233 (cid:12)→5 123123 (cid:12)→6 123312 (cid:12)→7

122313 (cid:12)→8 121233 (cid:12)→9 ¯112210 (cid:12)→10 010221 (cid:12)→11 ¯101122 (cid:12)→12
012210 (cid:12)→13 ¯10¯111 (cid:12)→14 00¯111 (cid:12)→15 1¯1221 (cid:12)→16 ¯111¯1 (cid:12)→17 11¯1 (cid:12)→18 C20

(32)

takes us step-by-step from the left of (26) to the right, if ‘α (cid:12)→m Cp’ means that
the (m−1)-class α can be immediately followed by a p-cycle in G | {1, . . . , p}.

December 4, 2025

tries
lieves
Lief: A leaf of a trie
Lieves: The plural of “Lief.”
preﬁx
bignum
Null pointers

24

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

In general, if C is any m-cycle in Gm = G | {1, . . . , m}, where G is any graph

with m or more vertices, there’s a unique sequence of transitions

0 = α0 (cid:12)→1 α1 (cid:12)→2 α2 · · · αj−1 (cid:12)→j Cm,

for some j < m.

(33)

For we obtain the j-class αj by ﬁrst removing all edges of Cm whose endpoints
both exceed j; then we use the extended frontier
Fj to name the j-conﬁg that
results. Conversely, any sequence (33) deﬁnes a unique m-cycle in Gm. This
one-to-one correspondence is the basis of Algorithm E.

(cid:8)

Notice that the size of a j-class α, that is, the number of equivalent j-conﬁgs
that it contains, is the number of paths of length j from 0 to α in such a sequence
of transitions. We’re counting Hamiltonian cycles by counting paths in a (large)
digraph of j-classes.

The main data structures for Algorithm E are two tries (see Section 6.3),
one for classes of the (m − 1)-conﬁgs already enumerated and one for classes of
the newly seen m-conﬁgs that they spawn. When the extended frontier
Fm has
size q, the trie for m-conﬁgs has q levels, representing successive digits of each
class name. Then there’s a “bottom” level of lieves, containing the class sizes.

(cid:8)

¯1

0

1

¯11

01

10

12

¯110

¯1101

¯111

¯111¯1

011

100

0110

1001

101

101¯1

121

1212

4

6

2

6

4

10

Fig. 125. A trie with q = 4, having Δ = 4 ﬁelds in each node.

For example, the six 16-classes in (28) and (29) might be represented by the
trie in Fig. 125. There’s one lief for every class name a1 . . . aq; and the path to
that lief, from the root at level 0, implicitly speciﬁes the digits a1, . . . , aq in turn.
More precisely, every node on level l, for 0 ≤ l < q, has Δ ﬁelds, representing
the potential digits (¯1, 0, 1, . . . ) that might appear in a name; the ﬁeld for al+1
links to the node or lief at level l + 1. In this way each node or lief on level l
represents all classes whose name begins with a particular preﬁx a1 . . . al.

Algorithm E uses two arrays, MEM and WT, to represent a trie. Each element
of MEM is a node that’s capable of holding Δ pointers, where Δ has been chosen
large enough to exceed al + 1 for any digit al. Each element of WT is a “bignum,”
a nonnegative integer that might be rather large; 128 bits or more are typically
allocated for each bignum, depending on the input graph. Trie nodes live in MEM;
trie lieves live in WT. For example, node 011 in Fig. 125 might be in MEM[9], and
lief 0110 might be in WT[3]. Then we’d have MEM[9][1] = 3 and WT[3] = 2. (Null
pointers, like MEM[9][0], are zero, and shown as blanks in this illustration.)

December 4, 2025

7.2.2.4 HAMILTONIAN PATHS AND CYCLES: DYNAMIC ENUMERATION

25

A sparse-set data structure is ideal for maintaining the frontiers as m grows.
There’s an array FR, which contains a permutation of the vertices, and a com-
panion array IFR for the inverse permutation. The ﬁrst q elements of FR are the
current frontier. More precisely, we have

FR[IFR[v]] = v,

for 1 ≤ v ≤ n;

and 1 ≤ FR[k] ≤ n,

for 0 ≤ k < n. (34)

sparse-set data structure
FR
IFR
0-origin and 1-origin indexing
MATE table
BMATE table
basic mate table

(cid:8)

Fm if and only if IFR[v] < q. Vertex uj in the discussion
Vertex v is part of
above corresponds to FR[j−1] in the computer’s internal representation. (These
conventions intentionally mix 0-origin and 1-origin indexing. Algorithm E wants
the vertices to be named {1, 2, . . . , n}, not {0, 1, . . . , n−1}, for ease in exposition.)
The main work of Algorithm E, which is to carry out the transitions from
(m−1)-classes to m-classes, is greatly facilitated by the use of a MATE table
somewhat like that of Algorithm H: MATE[j] = (−1, 0, k > 0) means that uj is
respectively (inner, bare, mated to uk). For example, class ¯1101 is equivalent to

MATE[1] = −1, MATE[2] = 4, MATE[3] = 0, MATE[4] = 2,

(35)

because both conventions mean that u1 is inner, u3 is bare, and that there’s a
subpath whose endpoints are u2 and u4. It’s easy to convert from one convention
to the other (see exercise 179).

The transition from m − 1 to m is basically straightforward. But the details
can be a bit tricky, because two frontiers and two MATE tables are involved.
The (m−1)-classes are characterized by a table OMATE[j] for 1 ≤ j ≤ q
=
(cid:0) ), while the m-classes
|
Fm−1| based on the “old” frontier
are characterized by a table MATE[j] for 1 ≤ j ≤ q = |
Fm| that’s based on
Fm = (u1, . . . , uq). Vertices that belong to both frontiers
the “current” frontier
(cid:8)
are represented by diﬀerent indices in OMATE and MATE.

Fm−1 = (u

(cid:2)
1, . . . , u

(cid:8)

(cid:2)
q

(cid:2)

(cid:8)

(cid:8)

Consider, for example, the case m = 8 in graph (26). The old frontier

F7
F8, the current frontier, is (9, 10, 17, 19, 20, 12), acc-
is (8, 9, 17, 19, 20, 10), while
(cid:2)
6 = u2. A subpath from vertex 9 to vertex 17
ording to (31). Thus u
(cid:8)
is represented by OMATE[2] = 3 in a 7-conﬁg, but by MATE[1] = 3 in an 8-conﬁg.
In general, if we set u0 = m, there’s a one-to-one mapping σ such that

(cid:2)
2 = u1 and u
(cid:8)

(cid:2)
u
j = ujσ,

for 1 ≤ j ≤ q

(cid:2)

; 1σ = 0.

(36)

Going the other way, if we set u

(cid:2)
0 = m + 1, there’s a one-to-one mapping τ with

uk = u

(cid:2)
kτ ,

for 1 ≤ k ≤ q0;

(37)

here q0 is deﬁned in (30). We have 1τ = 0 if and only if q0 = q

(see exercise 181).
Three main cases arise when we consider the m-classes that can follow a
given (m−1)-class, depending on whether vertex m is inner, bare, or outer in
that class. In other words, there are three cases, depending on whether OMATE[1]
is −1, 0, or > 1. The ﬁrst case is easy, because the given (m−1)-class is already
an m-class, and its MATE table is directly inherited from OMATE. We shall call
this the BMATE table (“basic mate table”):

(cid:2)

BMATE[k] =

December 4, 2025

(cid:9)

OMATE[kτ ]σ,
0,

if 1 ≤ k ≤ q0;
if q0 < k ≤ q;

OMATE[0] = 0,
(−1)σ = −1, 0σ = 0.

(38)

NBR
bignum
contribute()
try

26

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

In the other two cases, we start with the basic mate table, then add either
two edges from m to non-inner vertices (if OMATE[1] = 0), or one edge from m
to a non-inner vertex (if OMATE[1] > 1), in all possible ways. We set up an array
called NBR, so that the edges from vertex m to vertices > m can be represented as
m −−−uNBR[0], . . . , m −−−uNBR[r−1].
(39)

Algorithm E (Enumerate Hamiltonian cycles). Given a graph G on the vertices
{1, 2, . . . , n}, this algorithm computes CYC[m], the number of m-cycles in the
induced graph G | {1, 2, . . . , m}, for 3 ≤ m ≤ n. As described above, it uses
the arrays MEM, WT, OMEM, and OWT to represent tries; FR and IFR to represent
frontiers; NBR to represent neighbors; and several other auxiliary arrays, which
are described in various exercises that contain implementation details.
E1. [Initialize.] Set CYC[m] ← 0 (which is a “bignum”), for 3 ≤ m ≤ n. Set
FR[k] ← k + 1 and IFR[k+1] ← k, for 0 ≤ k < n. Set MEM[0][j] ←
OMEM[0][j] ← 0 for 0 ≤ j < Δ. Also set m ← 1, q ← 1, MEM[0][1] ← 1,
and WT[1] ← 1 (a “bignum”).

(cid:2)

E2. [Establish the trie for m − 1.] (At this point, FR and IFR represent the exter-
Fm−1, which has q elements. Arrays MEM and WT represent the
nal frontier
← q, p ← w ← 0; also swap OMEM ↔ MEM and
trie of (m−1)-classes.) Set q
OWT ↔ WT. (Only the base addresses change. Thus OMEM and OWT now repre-
(cid:8)
sent the (m−1)-classes. The previous contents of OMEM and OWT are now irrel-
evant; we’ll construct the trie of m-classes in their place. That trie contains
p nodes and w lieves as it is being built. It’s now empty, because p = w = 0.)
Change FR, IFR, q0, and q so that they now represent
Fm. (See exercise 187.)
(cid:2)
(cid:2)
(cid:0) so that
0, . . . , p
+ 1 pointer variables p
q
(cid:2)
(cid:2)
(cid:2)
(cid:0) , where
l] is node a
OMEM[p
1 . . . a
q
(cid:2)
(cid:2)
(cid:0) is the lexicographically smallest (m−1)-class. (See exercise 189.)
1 . . . a
a
q
(cid:0) .] Set up the OMATE table and the BMATE table.
E4. [Prepare to process a
(See exercise 179(a) and (36)–(38).) Go to step E5 if OMATE[1] < 0, to step
E6 if OMATE[1] = 0, otherwise to step E7.

E3. [Visit the ﬁrst (m−1)-class.] Set q

(cid:2)
l for 0 ≤ l < q

(cid:0)] is lief a

and OWT[p

(cid:2)
1 . . . a

(cid:2)
1 . . . a

(cid:8)

(cid:2)
q

(cid:2)
q

(cid:2)

(cid:2)

E5. [Contribute when m is inner.] Set MATE[k] ← BMATE[k] for 1 ≤ k ≤ q.

Then call contribute() (exercise 191) and go to E8.

E6. [Contribute when m is bare.] Call the subroutine try(NBR[i], NBR[j]) for

0 ≤ i < j < r (see exercise 193), and go to E8.

(cid:2)

(cid:2)
1 . . . a

(cid:2)
l for 0 ≤ l < q

+ 1 pointer variables p

E7. [Contribute when m is outer.] Call try(OMATE[1]σ, NBR[k]) for 0 ≤ k < r.
(cid:2)
(cid:2)
(cid:2)
(cid:0) so that
E8. [Visit the next (m−1)-class.] Set q
0, . . . , p
q
(cid:2)
(cid:2)
(cid:2)
(cid:0) , where
l] is node a
OMEM[p
1 . . . a
q
(cid:2)
(cid:2)
(cid:0) is the lexicographically smallest unvisited (m−1)-class, and return
a
1 . . . a
q
to E4.
(See exercise 189.) If all of the (m−1)-classes have been visited,
however, set m ← m + 1. Return to E2 if w > 0; otherwise terminate.
A superﬁcial glance at this algorithm leads to a natural question: Where does it
actually calculate the values CYC[3], CYC[4], . . . , CYC[n], which are the desired
outputs? The answer is that those values accumulate as m-cycles are discovered,
during the calls of try(i, j) in steps E6 and E7.

(cid:0)] is lief a

and OWT[p

(cid:2)
q

December 4, 2025

complete graph
OEIS
bignum
frontiers
colexicographic order

7.2.2.4 HAMILTONIAN PATHS AND CYCLES: DYNAMIC ENUMERATION

27

It’s quite instructive to watch Algorithm E in action when G is the complete

graph on n vertices. That’s when we get the most cycles. (See exercise 183.)

On the other hand, we’ve developed Algorithm E by considering a toy
problem that has only a few Hamiltonian cycles. Indeed, when we apply it to
the little graph (26), the results are that CYC[8] = CYC[14] = 1, CYC[17] = 2,
CYC[20] = 30, and CYC[m] = 0 otherwise. Ho hum. What’s the point? We obvi-
ously could have counted those cycles much faster by just visiting them directly.
But Algorithm E yields truly impressive results when we apply it to many
other graphs. For example, suppose G is the graph of knight moves on an 8 × 32
board. How many closed tours are possible? Answer:

2,989,043,104,279,785,843,506,369,864,414,419,975,166,020,

125,721,505,674,144,076,449,194,991,145,270,100.

(40)

Almost 3 quinvigintillion (see OEIS A193055)! That’s CYC[256]. Of course,
while computing this bignum, Algorithm E also discovers our old friend CYC[64],
the number of closed 8 × 8 tours, and many other interesting numbers along the
way (see exercise 196). And the running time for the entire calculation was just
66.5 teramems — about 2.5 teramems to go from 8 × k to 8 × (k+1) boards.

Let’s look more closely at the calculations that led to (40). The extended-
and-ordered frontiers of the 8 × 32 knight graph start small, but they rapidly fall
Fm has size 16 or 17:
into a pattern in which each

(cid:8)

F0 = (00);
F1 = (10, 21, 12);
(cid:7)
F2 = (20, 21, 12, 31, 02, 22);
(cid:7)
F3 = (30, 21, 31, 02, 12, 22, 01, 41, 32);
(cid:7)
F4 = (40, 01, 21, 31, 41, 02, 12, 22, 32, 11, 51, 42);
(cid:7)
F5 = (50, 01, 11, 21, 31, 41, 51, 02, 12, 22, 32, 42, 61, 52);
(cid:7)
F6 = (60, 01, 11, 21, 31, 41, 51, 61, 02, 12, 22, 32, 42, 52, 71, 62);
(cid:7)
F7 = (70, 01, 11, 21, 31, 41, 51, 61, 71, 02, 12, 22, 32, 42, 52, 62, 72);
(cid:7)
F8 = (01, 11, 21, 31, 41, 51, 61, 71, 02, 12, 22, 32, 42, 52, 62, 72);
(cid:7)
F9 = (11, 21, 31, 41, 51, 61, 71, 02, 12, 22, 32, 42, 52, 62, 72, 13);
(cid:7)
F10 = (21, 31, 41, 51, 61, 71, 02, 12, 22, 32, 42, 52, 62, 72, 13, 03, 23);
(cid:7)
F11 = (31, 41, 51, 61, 71, 02, 12, 22, 32, 42, 52, 62, 72, 03, 13, 23, 33);
(cid:7)
F12 = (41, 51, 61, 71, 02, 12, 22, 32, 42, 52, 62, 72, 03, 13, 23, 33, 43);
(cid:7)
F13 = (51, 61, 71, 02, 12, 22, 32, 42, 52, 62, 72, 03, 13, 23, 33, 43, 53);
(cid:7)
F14 = (61, 71, 02, 12, 22, 32, 42, 52, 62, 72, 03, 13, 23, 33, 43, 53, 63);
(cid:7)
F15 = (71, 02, 12, 22, 32, 42, 52, 62, 72, 03, 13, 23, 33, 43, 53, 63, 73);
(cid:7)
F16 = (02, 12, 22, 32, 42, 52, 62, 72, 03, 13, 23, 33, 43, 53, 63, 73);
(cid:7)
F17 = (12, 22, 32, 42, 52, 62, 72, 03, 13, 23, 33, 43, 53, 63, 73, 14);
(cid:7)
F18 = (22, 32, 42, 52, 62, 72, 03, 13, 23, 33, 43, 53, 63, 73, 14, 04, 24);
(cid:7)
F19 = (32, 42, 52, 62, 72, 03, 13, 23, 33, 43, 53, 63, 73, 04, 14, 24, 34);
(cid:7)
(cid:7)

(41)

and so on. (The vertices have row-column names (00, 10, . . . , 70, 01, 11, . . . , 71,
02, . . . ) here, instead of (1, 2, . . . , 256).) When 7 ≤ m ≤ 232,
Fm+8 turns out to
Fm, except that the vertices are shifted one column to the right.
be the same as

December 4, 2025

(cid:8)

(cid:8)

28

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

900,000,000

800,000,000

700,000,000

600,000,000

500,000,000

400,000,000

300,000,000

200,000,000

100,000,000

linear recurrence
generating function
periodic knight’s tours

0

8 16 24 32 40 48 56 64 72 80 88 96 104 112 120 128 136 144 152 160 168 176 184 192 200 208 216 224 232 240 248 256

0

m

Fig. 126. The number of lieves, Cm, in the tries for m-classes in the 8

32 knight graph.

×

The m-classes also fall into a pattern that’s periodic modulo 8; but they
don’t stabilize until m gets somewhat larger. It turns out that, when m mod 8 is
(0, 1, . . . , 7), the number Cm of m-classes is respectively (282609677, 233377701,
382538097, 461026164, 596486159, 601036842, 830339355, 833813266), for 72 ≤
m ≤ 240; thus it reaches its peak when m mod 8 = 7 and we’re closing out a
column. Similarly, the number Pm of nonlief trie nodes turns out to be respec-
tively (531992432, 470709142, 834186552, 1115100721, 1320322736, 1343754219,
1779294552, 1798400809), which is about (1.88, 2.02, 2.18, 2.42, 2.21, 2.24, 2.14,
2.16) nodes per class. Further statistics are discussed in exercise 198.

This periodic pattern proves that the number CYC[8n] of 8×n knight’s cycles
satisﬁes a linear recurrence, and has a generating function that’s a quotient of
(huge) polynomials. Empirically, the numbers are very close to .000000002465 ·
n
526.46

, for 16 ≤ n ≤ 32.

Periodicity mod 8 suggests that we can also construct “periodic knight’s

tours,” by ﬁnding classes α0, α1, . . . , α7 such that

α0 (cid:12)→m α1, α1 (cid:12)→m+1 α2, α2 (cid:12)→m+2 α3,

. . . , α7 (cid:12)→m+7 α0.

(42)

Such sequences of transitions occur, for example, when m mod 8 = 0 and α0 is
1234214300000000 or 01¯12314505004023 (see exercise 200). If we can also ﬁnd
transitions from 0 to α0, and from α0 to Cp for some p with p mod 8 = 0, we ob-
tain complete knight’s cycles with 8 rows and an unbounded number of columns:

(cid:9)Ir

(cid:9)J(cid:5)

(cid:9)q(cid:5)

(cid:9)J(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)J(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)J(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)J(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)J(cid:5)

(cid:9)(cid:128)(cid:4)

(cid:9)Cr

(cid:9)(cid:128)(cid:26)

(cid:9)s(cid:8)

(cid:9)(cid:10)(cid:4)

(cid:9)C(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)Ip

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)!"

(cid:3)J>

(cid:3)u>

(cid:3)J>

(cid:3)J>

(cid:3)J>

(cid:3)J>

(cid:3)J>

(cid:3)J>

(cid:3)J>

(cid:3)J>

(cid:3)J>

(cid:3)J#

(cid:3)v"

(cid:3)J(cid:26)

(cid:3)L(cid:8)

(cid:9)I"

(cid:8)J"

(cid:9)w"

(cid:3)u"

(cid:3)u"

(cid:3)w"

(cid:3)u"

(cid:3)w"

(cid:3)u"

(cid:3)u"

(cid:3)w"

(cid:3)u"

(cid:3)1"

(cid:3)n"

(cid:3)u(cid:26)

(cid:3)L(cid:8)

(cid:9)G>

(cid:3)^=

(cid:3)z=

(cid:3)a=

(cid:3)z=

(cid:3)a=

(cid:3)z=

(cid:3)a=

(cid:3)z=

(cid:3)a=

(cid:3)z=

(cid:3)a=

(cid:3)z=

(cid:3)a=

(cid:3)?(cid:26)

(cid:3)^(cid:8)

(cid:9)G"

(cid:8)A>

(cid:3)Q>

(cid:3)^>

(cid:3)A>

(cid:3)^>

(cid:3)A>

(cid:3)^>

(cid:3)^>

(cid:3)A>

(cid:3)^>

(cid:3)A(cid:26)

(cid:3)^(cid:26)

(cid:9)^=

(cid:9)a(cid:26)

(cid:3)^(cid:8)

(cid:9)G(cid:26)

(cid:3)A=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)z=

(cid:9)?M

(cid:3)(cid:130)(cid:8)

(cid:9)_(cid:26)

(cid:3)^U

(cid:9)fU

(cid:8)]U

(cid:8)fU

(cid:8)fU

(cid:8)]U

(cid:8)fU

(cid:8)]U

(cid:8)fU

(cid:8)fU

(cid:8)]U

(cid:8)f(cid:4)

(cid:8)C=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)(cid:5)

(cid:9)(cid:128)#

(cid:9)-=

(cid:9)G(cid:26)

(cid:3)A(cid:8)

(cid:9)d(cid:12)

(cid:8)^=

(cid:9)SF

(cid:9)(cid:131)F

(cid:9)cF

(cid:9){F

(cid:9)cF

(cid:9)cF

(cid:9){F

(cid:9)cF

(cid:9){F

(cid:9)cF

(cid:9)c"

(cid:3)6F

(cid:9)c(cid:26)

(cid:3)L(cid:8)

(cid:9)?(cid:29)

(cid:3)^>

(cid:3)J>

(cid:3)(cid:128)>

(cid:3)J>

(cid:3)(cid:128)>

(cid:3)J>

(cid:3)(cid:128)>

(cid:3)J>

(cid:3)(cid:128)>

(cid:3)J>

(cid:3)(cid:128)>

(cid:3)J(cid:4)

(cid:3)I>

(cid:9)J(cid:26)

(cid:3)A(cid:8)

(cid:9)G"

(cid:3)-(cid:4)

(cid:3)(cid:133)(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:18)=

(cid:9)S(cid:4)

(cid:9)IF

(cid:9)?7

(cid:3)b(cid:8)

(43)

(cid:9)E=

(cid:8)a=

(cid:3)(cid:131)=

(cid:3)a=

(cid:3)a=

(cid:3)a=

(cid:3)a=

(cid:3)a=

(cid:3)a=

(cid:3)a=

(cid:3)a=

(cid:3)a=

(cid:3)a>

(cid:8)]F

(cid:8)(cid:131)$

(cid:3)o(cid:8)

(cid:9)E=

(cid:8)EU

(cid:9)g"

(cid:8)(cid:22)"

(cid:2)(cid:133)"

(cid:2)6"

(cid:2)6"

(cid:2)(cid:133)"

(cid:2)6"

(cid:2)(cid:133)"

(cid:2)6"

(cid:2)6"

(cid:2)(cid:133)>

(cid:9)6R

(cid:8)(cid:131)[

(cid:3)Q(cid:8)

(cid:9)_F

(cid:9)z=

(cid:9){=

(cid:9)z=

(cid:9)a=

(cid:9)z=

(cid:9)a=

(cid:9)z=

(cid:9)a=

(cid:9)z=

(cid:9)a=

(cid:9)z#

(cid:9)Ǳ=

(cid:9)zF

(cid:9)a.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)ǱR

(cid:9){R

(cid:9){R

(cid:9)cR

(cid:9){R

(cid:9)cR

(cid:9){R

(cid:9){R

(cid:9)cR

(cid:9){R

(cid:9)c"

(cid:9)1"

(cid:9)1"

(cid:9)o.

(cid:9)b(cid:8)

These 8 × 16 tours become 8 × (k + 5) tours when the m-class α0 occurs k times,
for every k ≥ 1.

It’s fascinating to follow the course of the knight in labyrinthine tours like
this. Starting, for example, at the left of the lefthand tour, the knight will hop
all the way to the right, then left, then right, then left, right, left, right, and left
again. A knight traversing the righthand tour will reverse direction ten times!

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
(cid:26)
$
%
&
(cid:6)
(cid:129)
(
V
*
\
Y
(cid:7)
(cid:29)
(cid:5)
$
.
H
N
8
(cid:31)

*
P
(cid:7)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:26)
$
%
3
(cid:129)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
(cid:26)
%
&
H
(cid:13)
(
V

\
:
(cid:7)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
(cid:129)
(cid:31)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
$
@
3
N
(cid:31)

*
P
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
$
%
@
3
N

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
%
H
(cid:31)

9
:
(cid:2)
(cid:7)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
p
(cid:30)
(cid:31)
4
5
(cid:2)
(cid:7)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
&
(cid:6)
(
(cid:31)
0
(cid:2)
(cid:7)
(cid:3)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
3
(cid:129)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
%
H
(cid:13)
(cid:31)

9
:
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
%
H
(cid:129)
(cid:31)

*
9
Y
(cid:7)
(cid:8)
(cid:5)
$
%
(cid:6)
N
*
9
Y
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:12)
H
(cid:13)
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
4
W
9
X
Y
>
(cid:29)
(cid:20)
%
3
O
(cid:31)

9
:
(cid:2)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
(cid:29)
$
%
@
3
N
(cid:31)

*
9
Y
(cid:7)
(cid:8)
>
$
%
@
N
(cid:31)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
U
(cid:11)
$
@
3
N
(cid:31)
h
*
5
P
(cid:7)
>
(cid:29)
(cid:19)
M
%
3
N
x
K

e
9
(cid:24)
Y
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:12)
$
%
(cid:6)
’
(cid:14)
)
W
9
(cid:24)
Y
>
(cid:5)
.
(cid:6)
8
K
(cid:2)
(cid:7)
(cid:3)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
>
(cid:5)
$
.
(cid:6)
N
8
K
*
P
(cid:7)
}
$
.
N
8
K
*
P
(cid:0)
(cid:7)
(cid:28)
$
.
&
N
t
V
*
0
P
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
$
.
&
(cid:30)
N
/
K

*
0
P
(cid:7)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
(cid:26)
$
%
@
’
V
(cid:15)
*
9
5
,
(cid:0)
(cid:7)
[
.
N
O
8
(cid:31)
*
P
(cid:0)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
@
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
$
@
’
*
P
(cid:0)
(cid:7)
(cid:8)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
@
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
(cid:129)
(
*
\
Y
(cid:0)
(cid:7)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:23)
%
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
2
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
@
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:20)
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
.
3
8
)

(cid:2)
(cid:7)
(cid:3)
(cid:4)
7
8
)
9
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:19)
.
3
(cid:14)
8
K

(cid:16)
(cid:24)
(cid:2)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
(cid:30)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:26)
%
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
7
&
t
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
(cid:30)
(cid:14)
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
2
(cid:19)
(cid:20)
%
3
x
)

(cid:16)
9
(cid:24)
:
(cid:2)
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
2
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
(cid:4)
(cid:19)
7
(cid:14)
8
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:4)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:31)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
>
(cid:11)
(cid:19)
[
N
(cid:21)
V
(cid:15)
W
X
P
(cid:0)
.
N
O
8
*
P
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
7.2.2.4 HAMILTONIAN PATHS AND CYCLES: DYNAMIC ENUMERATION

29

Algorithm E is remarkably fast, but it needs lots of memory. Although the
frontier sets in (41) are rather large, the algorithm succeeds only because they
aren’t too large. No frontier has more than 17 elements; hence each trie node
needs to hold only 10 pointers (see exercise 195). And we’ve seen that no trie has
more than 1.8 billion nodes; hence each pointer needs to occupy only four bytes.
Therefore, with 40 bytes in each trie node and 48 bytes in each bignum, the
total bytewise memory requirement is roughly 2 billion times 40, plus 1 billion
times 48, namely 128 gigabytes per trie. (Exercise 204 shows, however, that this
memory requirement is somewhat pessimistic, because the trie of (m−1)-classes
can be greatly compressed.)

+

By making only a few changes to Algorithm E, we can extend it to “Al-
,” which counts the Hamiltonian paths of each induced subgraph
gorithm E
G | {1, . . . , m} instead of counting the Hamiltonian cycles. The idea is simply
to imagine a new vertex ‘∞’, following vertex n, with v −−− ∞ for 1 ≤ v ≤ n.
Hamiltonian paths of G | {1, . . . , m} are then equivalent to Hamiltonian cycles of
G | {1, . . . , m, ∞}. (See exercise 2.) The new vertex ‘∞’ becomes a new member
of every frontier. Exercise 209 has the details.

memory+
RAM
Hamiltonian paths
∞
Hamilton
OEIS
open knight’s tours
Chernov
Stertenbrink

+

For example, let’s go back to Hamilton’s original graph G in (26). We get a
Hamiltonian m-path in Gm = G | {1, . . . , m} for m ≤ 8 by taking an appropriate
subpath of 4 −−− 3 −−− 2 −−− 1 −−− 5 −−− 6 −−− 7 −−− 8 −−− 4, which is the 8-cycle
in the middle of (26). These are the only m-paths for m < 8, except that
4 −−− 3 −−− 6 −−− 5 −−− 1 −−− 2 also works when m = 6. By omitting any one edge
of the 8-cycle, we get eight 8-paths for m = 8; and there are two more, one of
which is 5 −−−1 −−−2 −−−3 −−−6 −−−7 −−−8 −−−4. The total number of Hamiltonian
m-paths in Gm, for m = (2, 3, . . . , 20), turns out to be respectively (1, 1, 1, 1,
2, 1, 10, 3, 12, 3, 16, 6, 32, 7, 44, 84, 120, 276, 1620).

Wow! Algorithm E

allows us to go way beyond (40) and to obtain the

exact number of open knight’s tours of size 8 × 32:

20,279,590,726,014,132,421,141,646,018,182,968,888,437,777,

268,855,614,013,516,231,312,347,225,658,967,818,240.

(44)

(See OEIS A389760 and exercise 206.) It’s roughly 6785 times as big as (40).
While computing this value, which is PATH[256], hundreds of smaller totals were
of course also found, including PATH[64]:

9,795,914,085,489,952.

(45)

This is the number of open knight’s tours on a normal chessboard, ﬁrst computed
by A. Chernov and G. Stertenbrink in 2014 by taking a weighted sum of 136
individual counts for diﬀerent choices of where to start and stop the tour.

The author’s computation of (44) was a bit of an adventure, lasting about
33 days on a machine with 2 terabytes of RAM. Again, periodic behavior began
to kick in when m passed 80, as in Fig. 126; but now the tries were about 8.61
times larger. Empirically, the number PATH[8n] of 8 × n open knight’s tours is
n
fairly well approximated by (.000000028 + .0000001n + .000000015n
) · 526.458
for 16 ≤ n ≤ 32. (See exercise 210.)

2

December 4, 2025

30

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

Directed and bidirected graphs. So far we’ve been discussing Hamiltonian
paths and cycles only with respect to garden-variety (undirected) graphs. But
they’re quite important in directed graphs too.

Let’s look, for example, at an 8-vertex digraph that can easily be analyzed

by hand. It’s based on the following matrix of football scores:

directed graphs–
football scores
Stanford GraphBase
Ivy League
4-cube

Brown

Colum- Cor- Dart- Har-
nell mouth vard

bia

Penn

Prince-
ton

Yale

Brown
Columbia
Cornell
Dartmouth
Harvard
Penn
Princeton
Yale

17

·
0
−
34
29
52
17
27
27

−
−
−
−
−
−

17
7
41
0 34
37
9
21
24
23 15
31
21

−
·
−
−
−
−
−
−

0

7
0

0
11
20
6
17
6 15
17 14
7 31

0
34
41 20
6

−
−
−
6
·
20 0
−
21 16
17 6
41 17

−
−
·
−
−
−
−
−

29 37
34
6
11 20
17

17

6 24
−
23 20
27 34

52 24
9
6
17 21
6
0
20

20
23 34
19 27

−
−
−
−
·
−
−
−

−
−
−
−
−
·
−
−

17 23
21 17
15 17
16
23
24 23
20

20
10 34

−
−
−
−
−
−
·
−

27 21
15 7
14 41
6 27
20 19
34 10
7

27
31
31
17
34
27
34

−
−
−
−
−
−
−
·

⎛

⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎜
⎝

⎞

⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎟
⎠

−
−
(The Stanford GraphBase includes data for the scores of all games played be-
tween the top 120 college football teams in the USA during the 1990 season — a
particularly memorable year. This matrix shows the “Ivy League” games. For
example, Brown beat Columbia, 17 to 0, but lost to Cornell, 7 to 34.)

7

(46)

8
2

We get a digraph with
Columbia, Brown
Columbia, Cornell
Yale, Dartmouth

→

Harvard, Dartmouth

→
Columbia, Harvard

→

→

→
Harvard, Princeton
Columbia, Yale

Brown
→
Cornell
→
Cornell
→
Dartmouth
Harvard
Penn
Yale

arcs from (46) by observing who beat whom:

Penn, Columbia
(cid:6)
→

(cid:7)
→
Harvard, Cornell
Brown, Dartmouth

Princeton, Cornell
Penn, Cornell
Columbia, Dartmouth

Brown,
→
Princeton,

→

Princeton, Dartmouth

Princeton, Penn

→
Brown, Princeton

→

→
Columbia, Penn

→
Dartmouth,

Penn, Yale

→
Brown,

→
Yale, Harvard

Cornell,

Brown,

→
→

→

→

Harvard, Yale

→
Penn, Yale

→
→
Does this digraph have a Hamiltonian cycle? If so, it will have to include the
Princeton, because that was Columbia’s only victory. It will also
arc Columbia
Cornell, because those were Dartmouth’s
have to include Penn
and Cornell’s only defeats. Then Cornell
Yale is also forced, because Yale’s only
→
other loss was to Dartmouth. . . . We soon discover two solutions, one of which is

Dartmouth

Princeton.

(47)

→

→

→

→

→

→

Yale

Harvard

Columbia

Princeton

Brown

→
and the other is the answer to exercise 211.

→

→

→

Penn

→

→

Dartmouth

Cornell

Yale

→

→

A vast number of interesting digraphs arises when we take an undirected
graph and assign an orientation to each edge. Consider, for example, the 4-cube,

00000000

0000

0000

0000

0000

0000
0000

0000

0000

0001

0011

0010

0000

0000

0100

0101

0111

0110

0000

0000

1100

1101

1111

1110

0000

0000

1000

1001

1011

1010

0000

00000000

0000

0000

0000

0000

0000
0000

,

(48)

December 4, 2025

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: (BI)DIRECTED GRAPHS

31

whose vertices are the 16 binary vectors of length 4, adjacent when they diﬀer in
just one bit position. (As in exercise 7.2.1.1–17, the 4-cube is represented here
as a torus, C4 C4, with arcs wrapping around from top to bottom and left to
right.) There are 64 Hamiltonian cycles with this orientation, one of which is

0000 −−→0001 −−→0011 −−→0010 −−→1010 −−→1011 −−→1001 −−→1101 −−→0101
−−→0100 −−→0110 −−→0111 −−→1111 −−→1110 −−→1100 −−→1000 −−→0000 .

(49)

(We know from Eq. 7.2.1.1–(26) that the non-oriented 4-cube has 1344 of them.)
A knight graph can be oriented in a particularly interesting way, if we insist
that the knight always moves counterclockwise with respect to some pivot point.
For example, the knight will continually whirl around the center of an ordinary
chessboard if and only if its moves have the following orientations:

4-cube
torus
knight graph
counterclockwise
anticlockwise: see counterclockwise
pivot point
whirling knight’s tours
angular velocity
chess pieces
Whirling kings

.

(50)

Do such whirling knight’s tours exist? Yes indeed; but they’re rare. Even
rarer are the tours that whirl around a pivot that lies southeast of the center(!):

(cid:9)I(cid:4)

(cid:9)Cr

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)Cr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)Cp

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)C(cid:4)

(cid:9)Cp

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)Ir

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)Cr

(cid:9)J(cid:26)

(cid:9)s(cid:8)

(cid:9)D"

(cid:3)D"

(cid:9)n(cid:4)

(cid:3)(cid:133)"

(cid:9)v"

(cid:3)n"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)D"

(cid:3)D"

(cid:9)(cid:133)2

P(cid:133)"

(cid:8)(cid:137)"

(cid:3)n"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)I"

(cid:8)v"

(cid:3)n"

(cid:3)u(cid:29)

(cid:3)u"

(cid:3)v"

(cid:3)u(cid:26)

(cid:3)L(cid:8)

(cid:9)G>

(cid:8)(cid:134)(cid:4)

(cid:3)g(cid:29)

(cid:9)(cid:135)R

(cid:3)S(cid:5)

(cid:9)u=

(cid:9)?M

(cid:3)(cid:130)(cid:8)

(cid:9)G>

(cid:8)^#

(cid:3)(cid:137)F

(cid:9)zF

(cid:9)c(cid:5)

(cid:9)u=

(cid:9)?[

(cid:3)(cid:130)(cid:8)

(cid:9)I"

(cid:8)^.

(cid:9)o>

(cid:9)(cid:134)=

(cid:8)z=

(cid:3)i=

(cid:9)(cid:136)(cid:26)

(cid:3)A(cid:8)

(cid:9)D>

(cid:7)(cid:134)[

(cid:3)jF

(cid:9)G(cid:26)

(cid:3)L(cid:28)

(cid:9)!=

(cid:7)?M

(cid:3)(cid:130)(cid:8)

(cid:9)D(cid:4)

(cid:3)](cid:4)

(cid:9)](cid:4)

(cid:9)Cr

(cid:9)|}

(cid:9)(cid:138)=

(cid:3)(cid:131)(cid:26)

(cid:3)A(cid:8)

(cid:9)E"

(cid:8)](cid:4)

(cid:9)(cid:133)(cid:28)

(cid:9)D=

(cid:3)z2

(cid:9)f=

(cid:8)(cid:136)(cid:26)

(cid:3)A(cid:8)

(cid:9)D>

(cid:7)^[

(cid:3)j=

(cid:9)E(cid:23)

(cid:8)A(cid:28)

(cid:9)!>

(cid:7)(cid:135)M

(cid:3)(cid:130)(cid:8)

(cid:9)G(cid:11)

(cid:8)^"

(cid:9)(cid:137)"

(cid:3)1"

(cid:9)1(cid:4)

(cid:3)(cid:133)(cid:29)

(cid:9)(cid:135)(cid:26)

(cid:3)A(cid:8)

(cid:9)E"

(cid:9)]"

(cid:9);"

(cid:9);$

(cid:3)o=

(cid:9)dF

(cid:8)?(cid:26)

(cid:3)L(cid:8)

(51)

(cid:9)D(cid:26)

(cid:3)^(cid:4)

(cid:9)]=

(cid:9)(cid:136)"

(cid:3)(cid:134)(cid:28)

(cid:9)1>

(cid:3)(cid:135)(cid:26)

(cid:3)A(cid:8)

(cid:9)D(cid:26)

(cid:3)^=

(cid:9)Gr

(cid:9)q(cid:4)

(cid:9)(cid:22)(cid:23)

(cid:9)AF

(cid:9)?(cid:26)

(cid:3)L(cid:8)

(cid:9)D"

(cid:9)v"

(cid:9);(cid:20)

(cid:9);(cid:4)

(cid:9)]=

(cid:9)(cid:136)R

(cid:9)?(cid:26)

(cid:3)L(cid:8)

(cid:9)E(cid:4)

(cid:8)]2

(cid:9)(cid:22)F

(cid:8)(cid:131)>

(cid:9)6(cid:4)

(cid:8)(cid:22)>

(cid:9)(cid:130)M

(cid:3)(cid:130)(cid:8)

(cid:9)E#

(cid:8)Ǳ}

(cid:9)(cid:138)>

(cid:0)(cid:22)U

(cid:8)(cid:22)"

(cid:8)(cid:22)=

(cid:9){[

(cid:3)(cid:130)(cid:8)

(cid:9)~#

(cid:0)~(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)2

(cid:9)(cid:22)"

(cid:8)(cid:22)=

(cid:9){M

(cid:3)(cid:130)(cid:8)

(cid:9)_"

(cid:9)ǱF

(cid:9){"

(cid:9)1#

(cid:9)1"

(cid:9)ǱF

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)Ǳ#

(cid:9)1#

(cid:9)ǱR

(cid:9)a"

(cid:9)1R

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1F

(cid:9){"

(cid:9)1F

(cid:9){.

(cid:9)b(cid:8)

Only 1120 tours of the former type exist, and only 4 of the latter. The lefthand
example is one of 16 that have central symmetry.

It turns out that all 1120 of the Hamiltonian cycles of the digraph deﬁned
by (50) have the property that they whirl around the center exactly seven times.
Equivalently, exactly seven of their arcs cross the “plumb line” that extends
vertically from the center. In fact, the tour shown in the middle example of (51)
maintains a fairly steady angular velocity: The number of steps between its seven
plumb-line crossings always diﬀers from 64/7 by less than 2. (This example, and
its left-right reversal, are the only such whirling knight’s tours. See exercise 228.)
The concept of whirling tours adds a new, relatively unexplored dimension
to the age-old study of the movements of chess pieces. Exercises 227–236 explore
some of the most basic questions related to them. Whirling kings are almost as
interesting as whirling knights! Many beautiful patterns arise.

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
$
%
&
(cid:6)
N
(
)
*
\
Y
(cid:7)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
#
(cid:29)
(cid:23)
3
(cid:13)
(cid:14)
)

(cid:16)
(cid:24)
(cid:8)
#
T
&
/
)
\
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
$
@
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
[
N
O
*
P
(cid:0)
(cid:8)
(cid:5)
(cid:19)
@
H
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:26)
%
(cid:13)
)
9
:
(cid:0)
(cid:7)
(cid:8)
.
(cid:6)
8
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
p
(cid:30)
(cid:31)
4
5
(cid:2)
(cid:7)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
$
‘
(cid:6)
N
(
(cid:31)
(cid:15)
*
0
5
P
@
N
O
*
P
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
(cid:30)
K

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
r
$
&
(cid:6)
N
(
(cid:31)
(cid:15)
*
0
5
P
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
‘
’
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
(cid:14)
e
9
(cid:24)
,
(cid:0)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
$
l
(cid:6)
N
(
(cid:31)
(cid:15)
*
0
5
P
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
(cid:129)
(
*
\
Y
(cid:0)
(cid:7)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:12)
3
(cid:13)
(cid:14)

(cid:16)
(cid:24)
(cid:8)
(cid:5)
%
@
(cid:6)
)
9
:
(cid:2)
(cid:7)
(cid:8)
.
8
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
$
l
(cid:6)
N
(
(cid:31)
*
0
P
(cid:7)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:19)
(cid:20)
%
(cid:21)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:4)
(cid:11)
.
8
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:11)
(cid:19)
[
N
(cid:21)
(cid:15)
W
X
P
(cid:0)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
@
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
$
%
&
(cid:6)
N
(
)
*
+
,
(cid:7)
>
(cid:4)
.
&
/
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
4
W
X
#
(cid:29)
(cid:19)
(cid:20)
%
3
(cid:21)
)

(cid:16)
9
(cid:24)
:
(cid:2)
#
7
&
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
.
&
(cid:30)
/
K

0
(cid:2)
(cid:7)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
@
(cid:129)
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
M
N
O
*
P
(cid:0)
(cid:8)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
(cid:6)
8
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
r
H
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
‘
N
(
*
+
,
(cid:0)
(cid:7)
(cid:19)
@
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
>
[
&
N
O
(
(cid:31)
*
0
P
(cid:0)
$
@
’
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
@
(cid:129)
(cid:15)
*
5
P
(cid:0)
(cid:7)
#
(cid:29)
(cid:20)
3
O
)

(cid:2)
(cid:8)
(cid:3)
#
T
&
/
)
\
:
(cid:0)
(cid:2)
(cid:7)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
(cid:5)
(cid:19)
@
H
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
‘
’
(
*
+
,
(cid:0)
(cid:7)
r
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
@
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
(cid:30)
K

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:11)
(cid:20)
&
O
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:4)
(cid:11)
[
&
N
O
(
(cid:31)
(cid:15)
*
0
5
P
(cid:11)
(cid:19)
M
3
N
x
h
e
(cid:17)
P
(cid:4)
(cid:19)
(cid:20)
%
x
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
.
3
(cid:14)
8
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
p
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:12)
$
’
(cid:14)
V
W
(cid:24)
P
(cid:0)
}
$
.
&
N
/
K
*
0
P
(cid:0)
(cid:7)
>
(cid:5)
$
.
&
(cid:6)
N
t
V
*
0
P
(cid:7)
(cid:5)
$
.
H
N
8

*
P
(cid:7)
#
(cid:29)
(cid:26)
%
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
T
&
H
/
V

\
:
(cid:2)
(cid:7)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
$
%
@
(cid:129)
(cid:14)
)
e
9
(cid:24)
,
(cid:0)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
@
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
$
@
3
N
(cid:31)
4
*
5
P
(cid:7)
M
%
N
O
*
9
Y
(cid:0)
(cid:8)
>
(cid:29)
(cid:26)
3
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
$
%
@
N
(cid:14)
)
W
9
(cid:24)
Y
(cid:0)
(cid:19)
.
(cid:14)
8
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:31)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
l
N
(
*
0
P
(cid:0)
(cid:7)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:12)
%
3
(cid:13)
(cid:14)

(cid:16)
9
(cid:24)
:
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
@
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
.
x
8
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
>
(cid:20)
.
O
8
K
(cid:0)
(cid:2)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
2
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
%
(cid:30)
(cid:14)
)

(cid:16)
9
(cid:24)
:
(cid:2)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:26)
&
(cid:13)
(
)
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:11)
(cid:20)
.
&
O
t
)
(cid:15)
0
5
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
H
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
&
N
(cid:14)
(
(cid:15)
W
\
X
Y
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:4)
(cid:19)
(cid:20)
%
(cid:21)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
.
3
(cid:14)
8
(cid:31)
4
(cid:16)
X
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
bidirected graph
oriented signed graph, see bidirected
bidirectional vs bidirected
arrows
angle brackets
introverted edge
extroverted edge
bidirected walk
trail
simple
bidirected cycle
bidirected path

32

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

We will soon be discussing Algorithm B, a variant of Algorithm H that
quickly ﬁnds patterns such as those in (49) and (51). But it turns out that
Algorithm B actually does considerably more: It visits all of the Hamiltonian
cycles in an arbitrary bidirected graph, a vast family of graph structures that in-
cludes directed graphs as a very special case. Therefore it behooves us to become
familiar with bidirectedness, a concept that cries out to be better known.*

The idea is actually quite simple and intuitive: The arcs of a bidirected graph
essentially have two arrows in place of one. If u and v are vertices, four kinds of
bidirected relationships are therefore possible: Either u (cid:3)(cid:3) v or u (cid:4)(cid:4) v or u (cid:3)(cid:4) v or
u (cid:4)(cid:3) v. The ﬁrst two cases are called directed edges, and they correspond to the
familiar relations u −−→ v and u ←−− v. (Our notation uses angle brackets ‘(cid:4)’ and
‘(cid:3)’ instead of arrows, because brackets look fairly nice and don’t take up much
space.) The third case, u (cid:3)(cid:4) v, is called an introverted edge; and the remaining
case, u (cid:4)(cid:3) v, is called an extroverted edge. In words, not symbols, we can verbalize
these four cases by saying “u to v” or “u from v” or “u intro v” or “u extro v.”
A single edge between u and v actually gives us only three diﬀerent relations
between those vertices, despite having four cases, because u (cid:3)(cid:3) v means the same
as v (cid:4)(cid:4) u. Similarly, u (cid:3)(cid:4) v means the same as v (cid:3)(cid:4) u, and u (cid:4)(cid:3) v means the
same as v (cid:4)(cid:3) u. On the other hand, sixteen diﬀerent relations between u and v
are actually possible, when u (cid:4)= v, because we might have any subset of the four
cases. For example, we might have u (cid:4)(cid:3) v and u (cid:4)(cid:4) v, but not u (cid:3)(cid:3) v and not u (cid:3)(cid:4) v.
A bidirected walk is obtained from a sequence of vertices joined by edges,
just as in an ordinary graph or directed graph; but we require the arrows next
to intermediate vertices to be identical. For example,

u (cid:4)(cid:4) x (cid:4)(cid:4) y (cid:4)(cid:3) z (cid:3)(cid:3) y (cid:3)(cid:3) x (cid:3)(cid:3) v

(52)

is a bidirected walk of length 6 between u and v. Contrariwise, a sequence like
u (cid:4)(cid:4) x (cid:3)(cid:4) y isn’t part of any legal walk; the arrows that surround x don’t match.
A walk is said to be a trail if its edges are distinct. In an ordinary graph,
a walk between two vertices always implies the existence of a trail between
those vertices; but (52) shows that we can’t always make such an inference
in a bidirected graph, because it includes the edge x (cid:4)(cid:4) y twice.

More formally, a sequence

u = t0 []0[]1 t1 []1[]2 t2 []2 · · · []l−1 tl−1 []l−1[]l tl = v,

(53)

where each []j is either (cid:4) or (cid:3), is a bidirected walk of length l between u and v. It’s
called simple if {t0, . . . , tl−1} are distinct and {t1, . . . , tl} are distinct. A simple
bidirected walk is called a bidirected cycle if t0 = tl and []0 = []l; otherwise it’s
called a bidirected path.

When all of the arcs of a bidirected graph are directed edges, it’s exactly
the same as a directed graph. When all of the arcs are introverted, the structure

* None of the textbooks on graph theory known to the author at the time this section was
written even mention the concept. Furthermore, some of them have unfortunately said that a
digraph is “bidirectional” if it has the property that u −−→v implies v −−→ u.

December 4, 2025

grid
knight graph
wazir moves, see grid moves
strictly alternating
grid moves
history
Ab¯u Bakr Muh. ammad ibn Yah. y¯a ibn al-‘Abb¯as a
Murray
Jelliss
top-down reﬂection
vertical symmetry
alternating moves
fers
alﬁl
Hamiltonian cycle of a bidigraph
bidigraph: Short for bidirected graph
Hamiltonian path of a bidigraph

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: (BI)DIRECTED GRAPHS

33

isn’t really interesting, because all walks have length 1. But we can get really
interesting structures when all of the arcs are either introverted or extroverted.
Indeed, suppose G and H are any two graphs on the same set of vertices.
Deﬁne u (cid:3)(cid:4) v if u and v are adjacent in G; also deﬁne u (cid:4)(cid:3) v if u and v are adjacent
in H. Then introverted and extroverted edges must alternate in any bidirected
walk. In particular, there can’t be any cycles of odd length.

For example, suppose G is the 4 × 4 grid on the 16 vertices {00, 01, . . . , 33},
and let H be the 4×4 knight graph on those same vertices. Then we have 00 (cid:3)(cid:4) 01,
00 (cid:3)(cid:4) 10, 01 (cid:3)(cid:4) 02, 01 (cid:3)(cid:4) 11, . . . , 32 (cid:3)(cid:4) 33 from G; and 00 (cid:4)(cid:3) 12, 00 (cid:4)(cid:3) 21, 01 (cid:4)(cid:3) 13,
01 (cid:4)(cid:3) 20, . . . , 23 (cid:4)(cid:3) 31 from H. This bidirected graph has 180 Hamiltonian cycles,
strictly alternating between knight moves and grid moves, one of which is

00 (cid:4)(cid:3) 12 (cid:3)(cid:4) 22 (cid:4)(cid:3) 03 (cid:3)(cid:4) 02 (cid:4)(cid:3) 23 (cid:3)(cid:4) 13 (cid:4)(cid:3) 32 (cid:3)(cid:4)

33 (cid:4)(cid:3) 21 (cid:3)(cid:4) 31 (cid:4)(cid:3) 10 (cid:3)(cid:4) 11 (cid:4)(cid:3) 30 (cid:3)(cid:4) 20 (cid:4)(cid:3) 01 (cid:3)(cid:4) 00.

(54)

Alternating patterns like this actually appeared very early in the history of
knight’s tours. A prominent Turkic polymath named Ab¯u Bakr Muh. ammad ibn
Yah. y¯a ibn al-‘Abb¯as al-S. ¯uli wrote a book on chess, a few decades after others
had devised the tours that we saw in (1) and (2) at the beginning of this section.
Besides discussing strategy, he presented several closed tours, including these:

32 35 30 25 8 5 50 55
29 24 33 36 51 56 7 4
34 31 26 9 6 49 54 57
23 28 37 12 1 52 3 48
38 13 22 27 10 47 58 53
19 16 11 64 61 2 43 46
14 39 18 21 44 41 62 59
17 20 15 40 63 60 45 42

37 14 16 35 33 18 24 31
15 36 34 17 19 32 30 25
13 38 48 11 21 26 28 23
39 12 10 49 27 20 22 29
9 42 40 47 61 50 52 63
43 8 46 41 51 60 62 53
45 6 4 59 57 2 64 55
7 44 58 5 3 56 54 1

49 42 40 51 9 34 36 11
47 52 54 45 39 12 14 33
41 50 48 43 37 10 8 35
55 44 46 53 15 32 38 13
61 22 16 63 5 26 28 7
19 56 58 21 31 64 2 25
17 62 60 23 29 6 4 27
59 20 18 57 3 24 30 1

. (55)

[His original treatise has been lost, but these tours were quoted by later authors.
See H. J. R. Murray, A History of Chess (Oxford, 1913), 171–172, 335–337.] The
knight’s cycle at the left is remarkable because, as observed by George Jelliss,
moves 26–40 are the top-down reﬂection of moves 11–25. The other two cycles
are even more remarkable, because they introduced a completely new idea, with
knight moves alternating with the moves of other ancient chesspieces called “fers”
and “alﬁl.” (A fers moves one step diagonally; an alﬁl hops twice as far.) Three
astonishing tours de force, constructed more than 1100 years ago!

The purpose of Algorithm B below is to visit every Hamiltonian cycle of
a given bidirected graph. But what exactly does that mean? In a bidigraph,
a (cid:4)(cid:4) b (cid:4)(cid:3) c (cid:3)(cid:4) a is quite diﬀerent from a (cid:4)(cid:3) b (cid:3)(cid:3) c (cid:3)(cid:4) a. So we can’t just “visit the
cycle (abc)”; we’ve got to specify also the relations between consecutive vertices.
In general, Algorithm B is supposed to visit every subset of edges that can
be expressed as a bidirected cycle having the form (53), where l is the total
number of vertices. A similar rule characterizes Hamiltonian paths: They’re the
subsets that can be expressed as bidirected paths according to (53), where l + 1
(not l) is the total number of vertices. (See exercise 242.)

December 4, 2025

34

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

Any bidirected graph B on n vertices {v1, . . . , vn} can be represented as
−
+
n }, where the edges
1 , v1, v

an ordinary graph G on 3n vertices {v
of G are v

+
1 , . . . , v
+
k for 1 ≤ k ≤ n together with

−
k −−−vk −−−v

−
n , vn, v

directed graphs
Tarjan
Karp
Hamiltonian matching

−
j −−−v
−
j −−−v

+
k ,
−
k ,

v
v

if vj (cid:4)(cid:4) vk in B;
if vj (cid:4)(cid:3) vk in B;

+
j −−−v
+
j −−−v

+
k ,
−
k ,

v
v

if vj (cid:3)(cid:4) vk in B;
if vj (cid:3)(cid:3) vk in B.

(56)

It’s easy to see that the Hamiltonian cycles in B correspond one-to-one with the
Hamiltonian cycles in G. (This idea, in the special case of directed graphs, is
due to R. E. Tarjan; see the famous paper by R. M. Karp, in Complexity of
Computer Computations (Plenum Press, 1972), pages 98 and 101.) Therefore
we don’t need a new algorithm; we could use our trusty old Algorithm H to visit
all the Hamiltonian cycles of B.

−
k and v

Let G(B) be the (ordinary) graph on 2n vertices {v

But we can do better than that, because every “unsigned” vertex vk is always
+
k when it’s in a Hamiltonian cycle. We can dispense

surrounded by v
with those unsigned vertices by slightly reformulating the problem.
+
−
n , v
1 , . . . , v

+
n } whose
edges are speciﬁed by (56). A Hamiltonian matching of G(B) is a set of n disjoint
+
edges for which the addition of n further edges v
k for 1 ≤ k ≤ n will form
a 2n-cycle. Hamiltonian matchings of G(B) correspond naturally to Hamiltonian
cycles of B; and we can visit them all by using almost the same method that
worked before, by simply adapting Algorithm H to the new setup.

−
k −−−v

−
1 , v

Indeed, Algorithm B almost writes itself, because most of the former steps

need little or no change. As usual, it’s instructive to work out the details.

Let’s state Algorithm B ﬁrst, and discuss its ﬁne points later.
The bidirected graph input to Algorithm B, like the undirected graph G
input to Algorithm H, has vertices v identiﬁed by integers, 0 ≤ v < n. But Algo-
rithm B actually works with the undirected graph G(B), which has 2n vertices;
vertex v of B corresponds to two vertices, v

= 2v+1, of G(B).

= 2v and v

−

+

Algorithm B (All directed or bidirected Hamiltonian cycles). Given a bidirected
graph B on the n vertices {0, 1, . . . , n−1}, this algorithm uses the data structures
discussed above to visit every Hamiltonian matching of the related graph G(B).
During every visit, the chosen edges are EU[k]−−−EV[k] for 0 ≤ k < n.

B1. [Initialize.] Set up the NBR and ADJ arrays (see exercise 250). Set the global
variables a ← e ← i ← l ← T ← 0. Also set VIS[v] ← IVIS[v] ← v and
MATE(v) ← −1 for 0 ≤ v < 2n. Set LLINK[2n] ← RLINK[2n] ← S ← 2n.
Finally, for every vertex v with DEG(v) = 1, set TRIG[T] ← v and T ← T+1.

B2. [Choose the root vertex.] Let CURV be a vertex of minimum degree, and
set d ← DEG(CURV). If d < 1, terminate (there is no Hamiltonian cycle).
If d = 1, set CURV ← −1, do step B4, and go to B6.

B3. [Force a root edge.] Set CURU ← NBR[CURV][d − 1 − i] (the last yet-untried
neighbor of CURV), and set EU[0] ← CURU, EV[0] ← CURV, e ← 1. Then get
started with CURU joined to CURV, as explained in exercise 251, and go to B6.

December 4, 2025

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: (BI)DIRECTED GRAPHS

35

B4. [Record the state.] Set CV(l) ← CURV, I(l) ← i, D(l) ← d, E(l) ← e,
S(l) ← S, T(l) ← T. For 0 ≤ k < S, set u ← VIS[k] and SAVE[2nl + u] ←
(thereby leaving “holes” in the SAVE stack). Then set
MATE(u), DEG(u)
u ← RLINK[2n]; while u (cid:4)= 2n, set ACTIVE[a] ← u, a ← a + 1, u ←
(cid:6)
RLINK[u]. Finally set A(l) ← a.

(cid:7)

(cid:7)

(cid:6)

B5. [Choose an edge.] Set CURU ← NBR[CURV][i], CURT ← MATE(CURU),
NBR[CURU][k],
CURW ← MATE(CURV), EU[e] ← CURU, e ← e+1. Call remarc
for k decreasing from DEG(CURU)−1 to 0. If CURT < 0 (CURU is bare),
CURU
makeinner(CURU), activate(CURU⊕1), and makemates(CURU⊕1, CURW). Oth-
erwise (CURU is outer), makemates(CURT, CURW) and deactivate(CURU).
B6. [Begin trigger loop.] Set j ← 0 if l = 0, else j ← T(l−1). Go to B10 if j = T.
B7. [Clothe TRIG[j].] Set v ← TRIG[j], and go to B9 if MATE(v) ≥ 0 or
IVIS[v] ≥ S (v isn’t bare). Otherwise go to B15 if DEG(v) = 0 (a Hamil-
tonian cycle is impossible). Set u ← NBR[v][0], EU[e] ← u, EV[e] ← v,
NBR[u][k], u
e ← e + 1, makeinner(v), and activate(v ⊕ 1). Call remarc
for k decreasing from DEG(u) − 1 to 0, except when NBR[u][k] = v.
(cid:7)
B8. [Take stock.] (We’ve just joined v to its only neighbor, u.) Update the
data structures as described in exercise 252, based on whether MATE(u)<0.

(cid:6)

B9. [End trigger loop?] Set j ← j + 1, and return to B7 if j < T.
B10. [Enter new level.] Set l ← l + 1, and go to B13 if e ≥ n − 1.
B11. [Choose vertex for branching.] Set CURV ← RLINK[2n], d ← DEG(CURV),
k ← RLINK[CURV]. While k (cid:4)= 2n, if DEG(k) < d reset CURV ← k and
d ← DEG(k); set k ← RLINK[k]. Go to B14 if d = 0. Otherwise set
EV[e] ← CURV and T ← T(l − 1).
B12. [Make CURV inner.] Call remarc

for 0 ≤ k < d
(thereby removing CURV from its neighbors’ lists). Then deactivate(CURV),
set i ← 0, and go to B4.

NBR[CURV][k], CURV

(cid:6)

(cid:7)

B13. [Visit a solution.] Set u ← LLINK[2n] and v ← RLINK[2n]. Go to B14 if
ADJ[u][v] = ∞. Otherwise set EU[e] ← u, EV[e] ← v, e ← n. Now visit
the n-cycle deﬁned by arrays EU and EV. (See exercise 253.)

B14. [Back up.] Terminate if l = 0. Otherwise set l ← l − 1.
B15. [Undo changes.] Set d ← D(l) and i ← I(l) + 1. Go to B14 if i ≥ d.
Otherwise set I(l) ← i, e ← E(l), k ← (l > 0? A(l − 1): 0), a ← A(l),
v ← 2n. While k < a, set u ← ACTIVE[k], RLINK[v] ← u, LLINK[u] ← v,
v ← u, k ← k + 1. Then set RLINK[v] ← 2n, LLINK[2n] ← v, S ← S(l),
T ← T(l). For 0 ≤ k < S, set u ← VIS[k] and
←
SAVE[2nl + u]. Finally set CURV ← CV(l). Go to B5 if l > 0.

MATE(u), DEG(u)

(cid:6)

(cid:7)

B16. [Advance at root level.] Set CURU ← EU[0]; remarc(CURV, CURU) and
remarc(CURU, CURV).
If
DEG(CURU) = 1, set TRIG[0] ← CURU and T ← 1; otherwise set T ← 0. If
DEG(CURV) = 1, set TRIG[T] ← CURV and T ← T + 1. Go to B3 if T = 0.
Otherwise set CV(0) ← −1, e ← 0, and go to B6.

(The previous edge CURU −−− CURV disappears.)

December 4, 2025

36

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

Algorithm B invokes the miniroutines makeinner, remarc, activate, deact-
ivate, and makemates, which were deﬁned in (19)–(23) for use in Algorithm H.
However, two changes are necessary: The condition ‘d = 2’ in (20) should become
‘d = 1’; and the value ‘n’ in (21) should become ‘2n’ (three times).

The main novelty here is the shift of focus to ﬁnding a Hamiltonian matching
of the special graph G(B), which has two vertices v
for each vertex of B.
This matching problem replaces the original goal of Algorithm H, which was to
ﬁnd a Hamiltonian cycle of an ordinary graph.

and v

−

+

For example, let’s consider a simple case where the given graph B has just

makeinner
remarc
activate
deactivate
makemates
perfect matchings
three-letter words
SSDIHAM

three vertices {0, 1, 2} and six bidirected edges,

0 (cid:4)(cid:4) 1,

0 (cid:4)(cid:3) 1,

0 (cid:3)(cid:3) 2,

0 (cid:3)(cid:4) 2,

In this case, by (56), G(B) has six vertices {0
(undirected) edges, which happen to form a cycle:

1 (cid:4)(cid:4) 2,
+
−

1 (cid:3)(cid:3) 2.
+
−

, 0

, 1

, 1

, 2

(57)

−

+

, 2

} and six

−

0

−−−1

+

−

−−−2

+

−−−0

−−−2

+

−

−−−1

−

−−−0

.

(58)

A 6-cycle always has two perfect matchings, and they turn out to be Hamiltonian;
but Algorithm B doesn’t know this, so let’s watch how it discovers the two
solutions. No vertex of G(B) has degree less than 2; therefore step B3 chooses
’.
a “root edge” to build upon. We shall assume that the root edge is ‘0
+
The ﬁnal cycle, after we add the required edges 0
to our Hamiltonian matching, will therefore contain the subpath

−−− 1
−

−−− 0

−−− 1

−−− 2

, 1

, 2

−

−

−

−

+

+

+

0

−−−0

−

−

−−−1

−−−1

+

.

(59)

−

−

and 1

This is the partial solution that is present when the algorithm ﬁrst reaches
+
are inner vertices; the endpoints 0
step B6. At that point 0
−
are outer vertices (and they are mates). The remaining vertices {2
+
currently bare. However, vertex 2
that joins it to an inner vertex has gone away. Therefore 2
list, and step B7 soon extends (59) to
+

has degree 1, because the edge 2

goes onto the trigger

and 1
+

} are
−

−−− 1

, 2
+

−

−

−

+

+

+

+

2

−−−2

−−−0

−−−0

−−−1

−−− 1

.

(60)

The algorithm now gets to level l = 1, and goes to step B13. Aha — the endpoints
of (60) complete a cycle! Hence {2
} is the ﬁrst
−−− 0
Hamiltonian matching found. (See exercise 254 for the sequel.)

−−− 2

−−− 1

, 1

, 0

−

−

−

+

+

+

In practice, Algorithm B is almost always applied to the special case in which
the input is just an ordinary directed graph, without introverted or extroverted
edges. In that case steps B1 and B13, which govern input and output, can be con-
siderably simpliﬁed, and the interface with users becomes much more intuitive.
(Exercise 256 has the details.) It’s therefore wise to have two implementations:
one for directed graphs only, and another for bidirected graphs in general.

arcowokidubayetajugnughimoownileicelfeziparevexisiqia

— SSDIHAM (26 October 2025)

December 4, 2025

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: (BI)DIRECTED GRAPHS

37

Who knows what I might eventually decide to say next? Please stay tuned.

December 4, 2025

Historical notes
grid graph
Rudyns’kyj
Vovk
Ukraine
Stone Age
Paleolithic
Mizyn (Cyrillic ‘Mi1zin’)
meander friezes
Greek pottery
icosahedra
knight’s tours
all Hamiltonian cycles
Roberts
Flores
directed graphs
backtracking
partial path
Wells
all Hamiltonian paths
undirected graphs
Selby
Imperial College
University of London
edge-oriented approach
link algorithm

38

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

History. There’s something inherently satisfying about a path that “hits all
the bases.” For example, the ancient artist who carved the pattern of Fig. 777
in a mammoth’s tusk might well have been trying to create a Hamiltonian-like
path in an implicit grid graph, before the dawn of recorded history!

Fig. 777. A pattern from the Old Stone Age. This detail
from a Paleolithic ivory carving, found near the present-day
village of Mizyn in northern Ukraine, illustrates interesting
ways to cover a grid, rotated 45◦, with a nonintersecting path.

Of course we cannot read the minds of people who lived c. 15,000 B.C.; but
we certainly can admire the wonderful sophistication that’s evident in this fas-
cinating artifact. [See M. Rudyns’kyj, Industrie en os de la station pal´eolithique
de Mizyn, interpr´et´ee par Fedir Vovk (Kyjiv: Vseukra¨ıns’ka Akademi(cid:18)ıa Nauk,
Kabinet Antropolohi˘ı im. F. Vovka, 1931), 66 pages, 32 plates.]

Fast forward now to 750 B.C., by which time “meander friezes” had become
well developed in many cultures, especially in Greek pottery (see exercise 360).
A few hundred years later, another kind of Hamiltonian pattern appeared
on icosahedra, as we saw near the beginning of this section. And considerable re-
search on knight’s tours began shortly after 800 A.D., as we’ve seen in (1) and (2).
But let’s jump to the computer age. The ﬁrst reasonably successful algo-
rithm for visiting all Hamiltonian cycles of a given graph was published by S. M.
Roberts and B. Flores in CACM 9 (1966), 690–694; 10 (1967), 201–202. They
actually considered directed graphs; but of course their method also handled
undirected graphs, because each edge u −−− v can be represented by a pair of
arcs, {u −−→v, v −−→ u}. Their procedure was an early instance of straightforward
backtracking: At each stage of the computation, a partial path v1 −−→ · · · −−→ vk
was extended by trying all possible successors to vk that hadn’t yet appeared.

Mark B. Wells, in §4.2.4 of his book Elements of Combinatorial Computing
(1971), presented a similar method, but for the task of visiting all Hamiltonian
paths, in undirected graphs. He explained how to detect certain impossible cases
early in the search, by backtracking whenever a partial path v1 −−− · · · −−− vk
wipes out all chances to reach a yet-untouched vertex v, namely when all of v’s
neighbors belong to {v1, . . . , vk}. He also considered the untouched v that have
exactly one neighbor in {v1, . . . , vk}: There must not be three such vertices; and
special restrictions apply when there are exactly two of them.

But Geoﬀrey R. Selby, in his Ph.D. thesis at Imperial College (University
of London, 1970), 264 pages, realized that an edge-oriented approach would be
much better. Instead of assigning vertices sequentially, he developed a “link algo-
rithm” for undirected graphs that has much in common with Algorithm H above.
Selby’s method was not as symmetrical as it could have been — he still retained
the concept of a “main” partial path v1 −−−· · · −−− vk; but he augmented that path
with a separate set of edges that it implies. Such edges, which form additional
partial paths, arise when an untouched vertex belongs to only two available edges.

December 4, 2025

Christoﬁdes
multi-path algorithm
Martello
MRV heuristic
Warnsdorf’s rule
Rubin
Selby
Wells
Hakami
Kocay
articulation point
bipartite
Chalaturnyk
data structures
Knuth
HAMDANCE
data structures
dancing links

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: HISTORY

39

Selby’s co-advisor at Imperial College, Nicos Christoﬁdes, worked out a
similar “multi-path algorithm” for directed graphs, and presented it in §10.2.3 of
his book Graph Theory: An Algorithmic Approach (1975). Then S. Martello im-
proved the algorithm further by incorporating the MRV heuristic, when selecting
the initial vertex v1 and when rank-ordering the neighbors of vk that are candi-
dates for vk+1. [ACM Trans. on Mathematical Software 9 (1983), 131–138.] (The
MRV heuristic had also been mentioned by Wells, who pointed out that neighbor
ranking makes no diﬀerence to the total running time when we are visiting all
of the solutions, because we are going to consider all choices of vk+1 anyway.
However, just as with Warnsdorf’s rule, MRV tends to ﬁnd the ﬁrst solution
much faster.) Curiously none of these authors realized that it would be much
better to use MRV symmetrically on the set of all endpoints of the current partial
paths or directed paths, as in Algorithm H or Algorithm B, instead of always
extending a “main” path by choosing a neighbor for vk at every stage. (Selby did
sometimes extend his main path at the left, if vertex v1 had a forced neighbor v0.)
Frank Rubin [JACM 21 (1974), 576–580], unaware of Selby’s or Wells’s
work, but inspired in part by S. L. Hakami [IEEE Region Six Conf. Record
(1966), 635–643], proposed a similar algorithm that was in some ways weaker
and in other ways stronger. His method repeatedly extended a single path at
the right, while marking certain oﬀ-path edges as “required” and other edges as
“deleted.” (For example, edges that touch a vertex of degree 2 were “required.”)
But again, there was only a single main path. He also tested reachability between
the path vertices and the remaining vertices; and he discussed preprocessing,
whereby a graph could sometimes be partitioned into subgraphs whose Hamil-
tonian cycles could be pieced together to obtain the overall cycles.

William Kocay [Discrete Math. 101 (1992), 171–188] realized that Selby and
Christoﬁdes’s multi-path algorithm could be made symmetrical, by giving equal
status to every subpath. (Curiously, however, he still distinguished the left and
right endpoints of subpaths. Instead of using MRV, the vertex that he chose for
branching was a right endpoint of maximum degree(!) — see exercise 129.)

Kocay also went further, by backtracking when the current subproblem could
not be completed to a Hamiltonian cycle because the current subgraph either had
an articulation point or was bipartite in an impossible way. (See exercise 130.)
This test was costly, but it could save considerable time in many cases.

Andrew Chalaturnyk (Master’s thesis, University of Manitoba, 2008, vi +
123 pages) made Kocay’s algorithm signiﬁcantly faster by designing data struc-
tures that allow it to backtrack eﬃciently. He improved the method also by
invoking tests for articulation points or bipartiteness only at judicious inter-
vals, when chances for eﬀective pruning of the search tree seemed most likely.
Without such pruning (which was optional), his program was rather similar to
Algorithm H, although considerably more complicated.

In unpublished experiments during 2001, Donald E. Knuth had developed a
symmetrical edge-based algorithm for Hamiltonian cycles in undirected graphs
that was comparatively simple. He called it HAMDANCE, because it used data
structures analogous to the dancing links of Algorithm 7.2.2.1X. Algorithm H,

December 4, 2025

SSHAM
sparse-set
SSBIDIHAM
Duby
Singmaster
L¨obbing
Wegener
BDD methods
McKay
Stertenbrink
corner wedge
Chalaturnyk
Denef
author
transfer-matrix method
dynamic programming
grid graphs
Stoyan
Strehl
Pettersson
border structure, see marked involution
P¨onitz
colorings
independent sets
acyclic orientations
knight’s tours
Elkies
Knuth
generating functions
symmetry
Euler
de Ruiter

40

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

which is called SSHAM because it uses sparse-set structures instead, was devised
in 2024, and followed by Algorithm B (SSBIDIHAM) in 2025.

Counting of knight’s tours on rectangular boards began with a 4-page note
by J. J. Duby, Etude #8 (Paris: IBM France, 22 October 1964), stating that
the 6 × 6 board has 9862 cycles. Subsequent early work is summarized in The
Games and Puzzles Journal 2, 15 (December 1997), 265.

David Singmaster [International Series of Numerical Mathematics 29 (Basel:
Birkh¨auser, 1975), 117–130] discussed Hamiltonian enumeration and gave a
23±3
heuristic ballpark estimate for the total number of 8 × 8 knight’s cycles: 10
.
Martin L¨obbing and Ingo Wegener [Electronic J. Combinatorics 3, 1 (1996),
#R5, 1–4 and comment] tried to count the 8×8 cycles by applying extended BDD
methods to each of roughly 380 million subproblems. Unfortunately something
went wrong, because the answer they got — more than 33 trillion — was not a
multiple of 4. This error stimulated Brendan D. McKay to compute the correct
value, as mentioned above, but without actually visiting the solutions.

The idea of a census is due to G¨unter C. Stertenbrink, who formulated the
“corner wedge” approach of exercise 152 in 2003, thereby gaining a factor of 8
because of symmetry. Andrew Chalaturnyk, as part of his thesis work in 2008,
generated the cycles for each of Stertenbrink’s 41790 canonical corner-bunches.
Working oﬀ and on, at times together with Yann Denef, Stertenbrink was able
in 2023 to compile a compressed database that contains representatives of all
13 trillion tours, occupying fewer than three terabytes of SSD storage.
(See
http://magictour.free.fr.) A census based on central wedges was indepen-
dently devised by the author in 2010; see FGbook, pages 494 and 495.

Algorithm E is based on an approach that is often called the “transfer-
matrix method” by mathematicians and physicists, or “dynamic programming”
by computer scientists. Those ideas were ﬁrst applied to Hamiltonian cycles only
in very special cases, such as the grid graphs Pm Pn; see, for example, Robert
Stoyan and Volker Strehl, J. Combin. Math. and Combin. Computing 21 (1996),
109–127. But Ville H. Pettersson [Electronic J. Combinatorics 21 (2014), #P4.7,
1–15] explained how to adapt the same methods to an arbitrary graph.

Indeed, the dissertation of Andr´e P¨onitz (Dr. rer. nat., Tech. Univ. Freiberg,
2004) developed a highly general approach to graph computations that included
not only Hamiltonian cycles but also colorings, independent sets, acyclic orien-
tations, and other problems galore. His “composition” framework solves such
problems dynamically by building up a graph one vertex and one edge at a time.
[See Operations Research Proceedings (2002), 383–388.]

Algorithm E was also inspired by work on knight’s tours. Early in 1994,
Noam Elkies and Donald E. Knuth independently obtained generating functions
for the number of closed 3 × n knight’s tours. They learned of each other’s work
during a chance encounter in Berkeley, but didn’t publish the results at that
time. Knuth [FGbook, Chapter 42] eventually extended this analysis to open
3 × n tours, and to tours with various kinds of symmetry.

Euler had proved in 1759 that there are no closed tours on a 4 × n board.
Johan de Ruiter realized that m×n boards for ﬁxed m > 4 were computationally

December 4, 2025

OEIS
Yang
Du
frontiers
anti-frontiers
equivalence classes
mate tables
tries
rook’s tours
grid graphs
king’s tours
triangular grid
simplex
OEIS
P¨onitz
Whirling knight’s tours
Bennett
Jelliss
Bidirected graphs
Edmonds
University of Michigan
Kotzig
perfect matching

+

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: HISTORY

41

feasible too; he obtained the results for m = 5 and m = 6 in 2010 (see OEIS
A175855, A175881). In the following year Yi Yang and Zhao Hui Du extended
the calculations to m = 7 and m = 8 (see OEIS A193054, A193055). They made
the key observation that it’s far better to use prior results by increasing the size
of the board by one cell at a time, not by one column at a time; so their method
was quite close to that of Algorithm E, in the special case of knight graphs.

Pettersson’s algorithm was sort of a dual to Algorithm E: Instead of working
with the frontiers Fm = {v | v > m and v −−− w for some w ≤ m}, he worked
with the “anti-frontiers” Bm = {v | v ≤ m and v −−− w for some w > m}. As in
Algorithm E, he passed from m − 1 to m by appropriately combining the sizes
of equivalence classes, characterized by mate tables. But instead of using tries,
he devised methods to compute the index of a weight directly from the mate
table of its class, in several families of highly structured graphs. For example, he
successfully enumerated not only the 26 × 26 rook’s tours (Hamiltonian cycles of
P26 P26), but also the 16 × 16 king’s tours (Hamiltonian cycles of P16 ×P16),
and the tours on a triangular grid with 20 vertices on each side (Hamiltonian
cycles of simplex (19, 19, 19, 19, 0, 0, 0)).

An interesting precursor to Algorithm E

appears implicitly in OEIS se-
quence A083386, which enumerates the open knight’s tours on a 5 × n board for
n ≤ 50. It was contributed by A. P¨onitz in 2003, as part of his thesis research,
curiously many years before the closed 5 × n tours had been counted.

Whirling knight’s tours were ﬁrst considered by E. W. Bennett [Fairy Chess
Review 6, 105 (February 1947), 72, problem 7159; 106 (April 1947), 82]. He
found a Hamiltonian path in the digraph (50), but was unable to construct a
Hamiltonian cycle. Almost 50 years went by before G. P. Jelliss discovered the
symmetrical cycle at the left of (51), as well as the three other classes of whirling
cycles that have circular symmetry [J. Recreational Mathematics 28 (1997), 234].
Bidirected graphs were named by Jack Edmonds, in the notes of some inﬂu-
ential lectures that he presented at the University of Michigan [“An introduction
to matching” (Summer 1967), 41–42; https://web.eecs.umich.edu/~pettie/
matching/Edmonds-notes.pdf]. The concept was actually implicit in a series of
papers by Anton Kotzig [Matematicko-Fyzik´alny ˇCasopis Slovenskeij Akad´emie
Vied 9 (1959), 73–91, 136–159; 10 (1960), 205–215], who considered the structure
of graphs that contain a perfect matching: The vertices of such graphs can be
(cid:2)
named {v1, v
j for 1 ≤ j ≤ n/2;
and the nonmatched edges essentially deﬁne a bidirected graph on n/2 vertices.

(cid:2)
n/2}, where n is even and vj −−− v

(cid:2)
1, . . . , vn/2, v

December 4, 2025

[This is a page-ﬁller so that the exercises will begin on a right-hand page.]

December 4, 2025

42

spanning
Hamiltonian
fourfold symmetry
symmetry
planar
icosahedron
concentric rings
4-cube
Gray binary code
draw the graph
unit-distance graph
graph drawing
dodecahedron
Hamiltonian path
generalized Petersen graph
Petersen graph
GP(n, k)
concentric-ring graph
enumeration of Ham cycles
one-in-three satisﬁability problem
NP-complete
cubic graph
satisﬁable
win
K2,1,1
induced subgraph
Wheatstone bridge
literals
clause gadget

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

43

EXERCISES

1. [15 ] We could save ourselves three syllables and three letters by saying “spanning
cycle” and “spanning path” instead of “Hamiltonian cycle” and “Hamiltonian path.”
Textbooks on graph theory could save lots of paper. Why doesn’t everybody do that?
K1. True

(cid:3) 2. [17 ] Join every vertex of graph G to a new vertex, obtaining G(cid:2) = G

or false: G has a Hamiltonian path if and only if G(cid:2) is Hamiltonian.

−−−

3. [M22 ] Reverse-engineer the rules by which Fig. 121’s vertices have been named.
4. [M30 ] The Hamiltonian cycle in Fig. 122(b) doesn’t look symmetrical. Show,
however, that it has fourfold symmetry when drawn on an undistorted dodecahedron.
5. [M20 ] A second glance at the graph depicted in Fig. 122(c) reveals that it actually

is obviously planar. Why?

6. [22 ] Draw the graph of the icosahedron in the style of Fig. 122(a), arranging the

vertices in three concentric rings.

7. [20 ] Draw the graph of the 4-cube in the style of Fig. 122(c), using Gray binary

code as the Hamiltonian cycle.

8. [HM25 ] Show that it’s possible to redraw the graph of the dodecahedron, Fig. 122,

in such a way that all lines between adjacent vertices have the same length.

(cid:3) 9. [M21 ] A Hamiltonian cycle on a planar cubic graph, such as the dodecahedron
in Fig. 121(b), can be described as a sequence of Ls and Rs denoting “left turn” and
“right turn” at each vertex encountered during the cyclic journey.

a) Prove that no Hamiltonian cycle on the dodecahedron can contain any of the
following subsequences: (i) LLLL; (ii) LRRL; (iii) LRLRLRL; (iv) LLRLRLL;
R swapped.
(v) LLRLRR; (vi) LLRLL; (vii)–(xii), subsequences (i)–(vi) with L

b) Therefore there is essentially only one cycle (and its dual obtained by L

R).

↔

↔

10. [24 ] For which vertices v of Fig. 122(a) is there a Hamiltonian path from 12 to v?
11. [M32 ] The generalized Petersen graph GP(n, k) is an interesting cubic graph with
1)(cid:2)
2n vertices

1, 0(cid:2), 1(cid:2), . . . , (n

and 3n edges

0, 1, . . . , n

{
{i

−

}

−
i(cid:2), i(cid:2)

(i + 1) mod n, i

−−−

−−−

(i + k)(cid:2) mod n | 0

i < n}.

≤

−−−

Figure 122(a) is the special case q = 5 of a general concentric-ring graph GP(2q, 2).

For which vertices v does the graph GP(2q, 2) have a Hamiltonian path from 0(cid:2) to v?

12. [HM28 ] How many Hamiltonian cycles exist in the graphs GP(2q, 2)?
14. [22 ] The one-in-three satisﬁability problem of exercise 7.2.2.2–517 is NP-complete.
For every such problem F , we shall construct a cubic graph G that is Hamiltonian if
and only if F is satisﬁable. Every edge of G corresponds to a Boolean variable; values
of the variables for which the true edges form a Hamiltonian cycle will be called a win.
as an induced subgraph also contains
, which has two edges that connect to other

the “Wheatstone bridge”
vertices. Show that those connecting edges must be true in every win.

a) A cubic graph that contains K2,1,1 =

b) For every clause C = (x

y

z) of F , where x, y, and z are literals, include the
below as part of G. Show that x + y + z = 1 in every win.

∨

∨

“clause gadget”

C

¯x

C

=

December 4, 2025

¯y

¯z

;

y =

x

⊕

x

x(cid:2)

y

.

y(cid:2)

44

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

c) If two edges x and y of G are replaced by the “XOR gadget” x

that x = x(cid:2), y = y(cid:2), and x = ¯y in every win.

y above, show

⊕

d) Suppose the clauses of F are

C1, . . . , Cm

. Use the gadgets above to construct

the desired graph G, starting with C1

Cm

.

{

}
. . .

16. [29 ] What’s the smallest connected cubic graph that is not Hamiltonian?

18. [M20 ] True or false: If a planar graph has a Hamiltonian cycle, so does its dual.
(cid:3) 20. [M30 ] (T. P. Kirkman, 1856.) Let G be a planar graph with n vertices and
3 (including the unbounded exterior face). For

with exactly αk k-sided faces for k
example, the graph of the dodecahedron, Fig. 122, has n = 20 and αk = 12[k = 5].

≥

a) If G is Hamiltonian, prove that integers ak exist such that 0

ak

αk and

2)ak = n

2. (For example, the dodecahedron has ak = 6[k = 5].)

≤

≤

n
k=3(k

−

−

(cid:14)

b) In a similar way, prove that the dodecahedron has no cycle of length 19.
c) Furthermore its vertices can’t be completely covered by two disjoint cycles.
d) Use (a) to prove that every Hamiltonian cycle in the planar 16-vertex
f

cubic graph G shown here must include the edges a

f .
e) Use (a) to decide whether any of the following graphs are Hamiltonian:

d, e

b, c

−−−

−−−

−−−

(i)

;

(ii)

;

(iii)

b

d

c

a

e

.

XOR gadget
gadgets
planar graph
dual
Kirkman
planar graph
faces
dodecahedron
cycle cover
benchmarks
perfectly Hamiltonian
edge coloring
cubic graphs
Tutte gadget
pentagonal prism
generalized Petersen graphs

21. [M25 ] Large graphs that contain no Hamiltonian cycles can often be useful bench-
marks. Construct inﬁnitely many cubic planar graphs that fail to satisfy exercise 20(a).

24. [M28 ] A cubic graph is called perfectly Hamiltonian if its edges can be 3-colored
in such a way that the edges of any two colors form a Hamiltonian cycle.

a) Which of the cubic graphs on 8 vertices are Hamiltonian? Perfectly Hamiltonian?
b) Prove that a planar cubic graph can be perfectly Hamiltonian only if there are
3 such that ak + bk + ck + dk = αk
2)bk =

nonnegative integers (ak, bk, ck, dk) for all k
is the number of k-faces as in exercise 20(a), and

2)ak =

k(k

k(k

≥

k(k

2)ck =

k(k

2)dk = (n

−

(cid:14)

−

(cid:14)

−

27. [M21 ] The Tutte gadget is a useful 15-vertex graph fragment

−
2)/2, where n is the number of vertices.

−

(cid:14)

(cid:14)

T

=

b a

f e

d

that can be obtained by removing vertex c from the 16-vertex graph in exercise 20(d).
a) Prove that every Hamiltonian path in a graph that contains the gadget must use

the edge at the bottom of the T.

b) Prove that no Hamiltonian path in the pentagonal prism GP(5, 1),

, includes

the edges of two nonconsecutive “spokes.”

c) Therefore none of the following 38-vertex graphs are Hamiltonian:

TT

TT

T

T

T

T

T

T

T

T

December 4, 2025

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

45

d) Are any two of those six graphs isomorphic to each other?

30. [20 ] Each letter in a Græco-Roman icosahedron can be placed three ways within
its triangular face, depending on the choice of “bottom edge” (except that Δ and O
are symmetric). From this standpoint, the fact that Π and Y share the same bottom
edge, in the text’s example from the British Museum, is a bit disconcerting.

Redesign that layout for the 21st century, so that (i) Roman letters A, B, . . . , T re-
place the Greek ones; (ii) the bottom edge of a letter’s successor is always the upper left
or upper right edge of the current letter; and (iii) T is adjacent to A, completing a cycle.
(cid:3) 33. [M20 ] Suppose G is an n-vertex graph that has H Hamiltonian cycles and h
Hamiltonian paths that aren’t cycles. (Thus, there are H sets of n edges whose union
is a cycle, and h sets of n
1 edges whose union is a path but not a cycle.) Let
G(cid:2) =
G be the (n + 1)-vertex graph obtained from G by adjoining a new vertex
that’s adjacent to all the others. How many Hamiltonian cycles does G(cid:2) have?
35. [M25 ] A close look at (1) shows that al-‘Adl¯ı’s closed tour is traced by a “thread”
that weaves alternately over and under itself at each crossing, forming a “knot.”

{∗} −−−

−

a) Prove that every closed knight’s tour can be drawn as such a knot.
b) On the other hand, the over-under rule is violated four times in Ibn Man¯ı‘’s open
tour. Prove that every drawing of his tour must necessarily have at least four such
exceptions to the rule.

isomorphic
Græco-Roman icosahedron
British Museum
Hamiltonian paths that aren’t cycles
al-‘Adl¯ı
path diagrams
weaves
knot
alternating knot diagrams
Ibn Man¯ı‘
Rudrat.a
sloka
fractured English
poem
Chaturanga
elephant
(s, t)-path: A path from vertex s to vertex t.
elephant’s tours
elephant digraph
trunk moves
quatrain
nonsense verse
Someshvara
path diagrams
Warnsdorf’s rule

×

×

8 knight’s tours are possible?

8 knight’s tours that (i) preserve the syllables of Rudrat.a’s sloka,

36. [22 ] Find 4
but diﬀer from (2); (ii) preserve the fractured English syllables of (4).
37. [22 ] How many 4
38. [25 ] Write a two-verse English poem for Rudrat.a’s 4
8 tour, analogous to (6).
40. [25 ] The variant of Chaturanga played in Rudrat.a’s day used a curious piece called
an elephant (gaja) instead of a chess bishop. This piece had only
ﬁve moves: One step forward or one step diagonally, representing
the elephant’s trunk and its four legs. For example, an elephant
8 board by following the (s, t)-path illustrated here.
can tour a 4

×

t

s

×

Represent this half-tour with a two-verse poem in English.
(cid:3) 41. [M32 ] This exercise classiﬁes all elephant’s tours on an m

n board, for m, n

2.

≥

×

×

n elephant digraph. How many arcs does it have?

a) Let Emn be the m
b) Does Emn have a closed tour (a Hamiltonian cycle), for some values of m and n?
c) The open elephant’s tour in exercise 40 begins at the bottom left corner of E48.
Show that there’s also an open tour that begins at the top left corner of E48.
d) Prove that every elephant’s tour must begin or end in the top row, when m > 2.
e) Similarly, prove that every such tour must begin or end in the bottom row.
f) Characterize all m
g) Characterize all m
h) Explain how to compute the number of Hamiltonian paths of Emn that begin at

n elephant’s tours that begin in the top row.
n elephant’s tours that begin in the bottom row.

×
×

a given vertex s and end at a given vertex t.
42. [30 ] Find a cycle of elephant moves on the 8
two of the cells, and (ii) has the fewest “trunk moves” among all such cycles.
44. [18 ] Using the syllables (7), construct a knight’s tour quatrain that rhymes.
46. [19 ] Draw Someshvara’s tour (8) in the style of (1).
50. [19 ] The text describes only one scenario for moves 9, 10, . . . , that might extend
the partial tour (10). What other paths are consistent with Warnsdorf’s rule?

8 chessboard that (i) visits all but

×

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
46

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

×

51. [21 ] What paths does Algorithm W construct when G is the graph of knight
5 board, s is cell 00, r = 1, and t1 is cell 44 (the corner opposite 00)?
moves on a 5

52. [20 ] What is the behavior of Algorithm W if ti = tj for some i

= j?

(cid:3) 53. [M21 ] Randomize Algorithm W, by changing step W5 so that each candidate u is
chosen with probability 1/q when there’s a q-way tie for the minimum number of exits.
Hint: There’s a nice way to do this “on the ﬂy” without building a table of candidates.

55. [20 ] How many of the 63 moves in the historic knight’s tour (1) by Ibn Man¯ı‘
agree with Warnsdorf’s rule? Consider also the closed tour of al-‘Adl¯ı, with the same
opening moves v1 and v2, as well as the open tour of Someshvara in exercise 46.

56. [20 ] Algorithm W sometimes moves to a “dead end” vertex (from which there’s
no exit), even though it could prolong the path by making a diﬀerent choice. Discuss.
(cid:3) 57. [21 ] Design an algorithm to compute the tree of all possible paths that might be
. Also compute, for each path,

computed by Algorithm W, given G, s, and
the probability that it would be obtained by the algorithm of exercise 53.

t1, . . . , tr

{

}

59. [21 ] What are the longest and shortest paths obtainable in the 8
8 knight graph
when the anti-Warnsdorf rule is used? (Move always to a cell with the most exits.)
Compare those results to the behavior of Algorithm W.

×

n knight graph: The SGB graph board(m

×

Randomize
Ibn Man¯ı‘
al-‘Adl¯ı
Someshvara
anti-Warnsdorf
m
concentric-ring graphs
generalized Petersen graphs
Warnsdorf’s rule
grid graph
n-cube
update(u1, . . . , ut)
Euler
hash table
linked lists
null
One-sided ﬂips
canonical form
lollipop method, see one-sided ﬂips
cubic
3-cube
perfectly

60. [22 ] Study empirically the behavior of Algorithm W on the concentric-ring graphs
Rq = GP(2q, 2) of exercise 11, for 6
10. What is the probability of obtaining
≤
(a) a Hamiltonian path? (b) a Hamiltonian cycle, when no target vertex is speciﬁed?
(c) a Hamiltonian cycle, when there’s a single target vertex with s

t1?

≤

q

×

62. [16 ] Prove that Algorithm W always ﬁnds a Hamiltonian path when G = Pm Pn
is the m

n grid graph, s = (0, 0) is a corner vertex, and r = 0.

(cid:3) 63. [M30 ] Prove that Algorithm W always ﬁnds a Hamiltonian path in the special
P2 is an n-cube and r = 0.
(cid:3) 65. [25 ] Is there a Hamiltonian graph for which Algorithm W always fails to ﬁnd a

case when G = P2 P2

· · ·

Hamiltonian path, regardless of the starting point and the ordering of arcs?

70. [11 ] Show that step F4 sometimes calls ‘update(u1, . . . , ut)’, which does nothing.

71. [M20 ] Euler believed that his method for discovering tours was “safe” and “in-
fallible”; but (16) is a case where it fails to ﬁnd a cycle. Construct arbitrarily large
Hamiltonian graphs for which Algorithm F can in fact get stuck with paths of length 10.

−−−

≤

73. [21 ] Discuss implementing the dictionary of Algorithm F with a hash table based
on linked lists. If the entry for each path links to the number of the previous path that
belongs to the same list, step F6 can regard all links

p2 as null.

75. [M23 ] (One-sided ﬂips.) Simplify Algorithm F so that it ﬂips subpaths only at
the right, and doesn’t distinguish between paths and cycles; call the resulting procedure
“Algorithm F−.” (More precisely, Algorithm F− never goes to step F5; it omits the
second update in step F4; and it doesn’t put paths into canonical form.)

a) Suppose Algorithm F− is applied to a Hamiltonian path v1

vn in a cubic
graph G. Show that it constructs a cycle of Hamiltonian paths, each beginning
with v1, and illustrate this cycle when G is the 3-cube.

−−−· · · −−−

b) Furthermore the number of cyclic Hamiltonian paths in that cycle is even.
c) Moreover, the number of Hamiltonian cycles containing any given edge is even.
d) Every cubic Hamiltonian graph therefore has at least three Hamiltonian cycles.
e) Every cubic graph with exactly three Hamiltonian cycles is perfectly Hamiltonian.

December 4, 2025

(cid:12)
7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

47

77. [M26 ] The Cameron graph Cn of order n is a planar cubic graph on the 8n + 2
j
vertices {ij | 0
≤
i3
i8
i5
i4
−−−
all integers i; replace all vertices ij for i < 0 by 0, and all ij for i

deﬁned by the relations i7
(i+1)5, and i8

i1
i2
−−−
−−−
(i+1)1 for
−−−
. For example,

i < n, 1
i7
i6

0,
∪ {
i2, i3

(i+1)6, i4

∞}
−−−

≤
−−−

≤
−−−

n by

−−−

−−−

−−−

−−−

−−−

8}

≥

∞

01

02

03

04

15

16

17

18

21

22

23

24

35

36

37

38

C4 =

0

∞ .

05

06

07

08

11

12

13

14

25

26

27

28

31

32

33

34

a) Prove that the involution ij
b) Prove that Cn has exactly three Hamiltonian cycles (one of which is the “obvious”

j) is an automorphism of Cn.

i)(9

↔

(n

−

−

−

1

Cameron graph
planar cubic graph
involution: perm of order 2
ﬂips
mate
concentric-ring graphs
generalized Petersen graphs
Beluhov
equivalent
Forcibly Hamiltonian degrees
degree seq of graph
complete graph
ﬂips
degree sequence
Nash-Williams
r-regular

cycle αn = 0

01

02

03

07

06

05

0).

−−−

−−−

−−−

−−−· · · −−−∞ −−−· · · −−−

−−−

−−−

−−−

c) Compute the number cn of one-sided ﬂips needed to go from αn to its mate βn
01, in the sense of answer 75(c), for 1
2 + 10 ﬂips go from αn to βn with respect to 01

with respect to 0
−−−
d) Surprise! Exactly cn
e) How many ﬂips go from αn to its mate γn with respect to (i) 0

0.
05? (ii) 05

−−−

≤

≤

9.

0?

n

−

−−−

−−−

78. [22 ] Study empirically the behavior of Algorithm F on the concentric-ring graphs
Rq = GP(2q, 2) of exercise 11, for 6
10 and q = 100. Let t = 1, and choose
≤
v1 at random; also randomize the order in which a vertex’s neighbors are examined.
Estimate the probability of obtaining (a) a Hamiltonian path; (b) a Hamiltonian cycle.
How many nontrivial calls of update are typically needed, before succeeding?

≤

q

79. [M32 ] (N. Beluhov, 2019.) Say that two Hamiltonian paths or cycles are equiv-
alent if they can be transformed into each other by Algorithm F.

a) Find a graph with two inequivalent cycles.
b) Can a graph have arbitrarily many pairwise inequivalent cycles?

80. [M20 ] For which q1, . . . , qs, t is the graph (Kq1
81. [M27 ] (Forcibly Hamiltonian degrees.) Sometimes we can conclude that a graph is
Hamiltonian just by knowing that it has lots of edges. If n > 2 and the vertices of G have
dn, we shall prove that G is Hamiltonian whenever
respective degrees d1

Kt Hamiltonian?

⊕ · · · ⊕

Kqs )

−−−

d2

≤ · · · ≤
≤
k < n/2 and dk

1

k implies dn

k

−

n

k.

(

)

∗

n
2

a) If G satisﬁes (

≤
) and has m <

prove that G contains two nonadjacent vertices
{
b) Continuing (a), let G0 = G; and let Gk+1 = Gk

≤
∗
edges, so that G is not the complete graph Kn,
n.
≥
vk
, where uk /
vk
−−−
m. Explain how to
and deg(uk) + deg(vk)
construct a Hamiltonian cycle in Gk, given a Hamiltonian cycle in Gk+1. (Since
G(

with deg(u) + deg(v)
}
uk
n
∪ {
2

m = Kn is Hamiltonian, so too is G0.) Hint: Use ﬂips as in Algorithm F.

n in Gk, for 0

−−−
−

n
2)−

k <

u, v

≥

−

≥

≤

}

(cid:15)

(cid:16)

(cid:15)

(cid:16)

82. [M25 ] If condition (
) fails in G for at least one value of k, show that there’s a
∗
non-Hamiltonian graph G(cid:2) whose degree sequence d(cid:2)1
d(cid:2)1,
d(cid:2)2
d(cid:2)n. (In this sense exercise 81 is the best possible result of its kind.)
d2
83. [M30 ] (C. S. A. Nash-Williams.) Let G be an r-regular graph with 2r + 1 vertices.

d(cid:2)n satisﬁes d1

d(cid:2)2, . . . , dn

≤ · · · ≤

≤

≤

≤

≤

a) Prove that r is even.
b) Prove that G has a Hamiltonian path u0
c) If G isn’t Hamiltonian, show that u0
uj
d) If G isn’t Hamiltonian, show that it has a cycle v1
e) Conclude that G is Hamiltonian. Hint: Suppose v0

−−−
uj

−−− · · · −−−
1 /
−
−−−
v2
vj

⇐⇒

−−−

−−−

u1

u2r.
u2r, for 1 < j < 2r.
v1.

v2r
j is odd.

−−−

−−−· · · −−−

−−−

⇐⇒

December 4, 2025

Erd˝os
traceable
nontraceable
length
knight graph
circumference
biconnected graph
Moon
Hamiltonian-connected
Coxeter graph
cubic graph
automorphisms
Sims table
vertex-transitive graph
edge-transitive graph
hypohamiltonian graph
cycle covers
ﬂower snark graph
planar

48

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

84. [M28 ] What’s the smallest number of edges for which condition (
forces an n-vertex graph to be Hamiltonian?
85. [HM21 ] (P. Erd˝os, 1962.) Let f (n, k) =
f (n,
g(n, k) edges and n vertices, where every vertex has degree
with more than g(n, k) edges is Hamiltonian. Hint: When is f (n, k)

, and g(n, k) = max(f (n, k),
k < n/2, there’s a non-Hamiltonian graph with
k. But every such graph

) in exercise 81

∗

)). Prove that if 1

f (n, k + 1)?

1)/2

+ k

(n

≤

−

≥

−
2

(cid:15)

(cid:16)

(cid:16)

(cid:17)

n

k

2

(cid:3) 86. [HM25 ] A graph is called traceable if it has a Hamiltonian path. Continuing
exercise 85, determine the largest possible number of edges in a nontraceable n-vertex
graph for which the degree of every vertex is k or more. Hint: Let the function
ˆf (n, k) =
+ k(k + 1) play the role of f (n, k) in that exercise.
88. [M27 ] The length of a graph is the number of edges in its longest path. (For
example, the 4

(cid:16)
4 knight graph has length 14.)

1
2

(cid:15)

−

−

n

k

a) Let G be a connected graph whose n vertices each have degree k or more, where

×

≥

k < n/2. Prove constructively that the length of G is at least 2k.
b) Prove that an n-vertex graph of length l has at most nl/2 edges.
2
(l + 1)
c) Exhibit an n-vertex graph of length l and at least nl/2
/8 edges.

−

(cid:3) 89. [M31 ] The circumference of a graph is the number of edges in its longest cycle.
4 knight graph has circumference 14.)

(For example, the 4

a) Let G be a biconnected graph whose n vertices each have degree k or more, where

×

≤

1 < k

n/2. Prove constructively that the circumference of G is at least 2k.

b) Prove that an n-vertex graph of circumference c has at most (n
nc/2
c) If c>2, exhibit an n-vertex graph of circumference c and

1)c/2 edges.
2
(c + 1)
/8 edges.
90. [16 ] True or false: The length of G is two less than the circumference of K1
G.
93. [M25 ] (J. W. Moon, 1965.) A graph that has a Hamiltonian path between every
pair of vertices u

= v is called Hamiltonian-connected.

−
−

−−−

≥

a) True or false: Every vertex of a Hamiltonian-connected graph has degree
b) Construct a Hamiltonian-connected graph on n

4 vertices that has the smallest
possible number of edges (for example, 8 edges when n = 5; 9 edges when n = 6).

≥

≥

3.

(cid:3) 95. [M28 ] The Coxeter graph is a remarkable cubic graph
are connected by
bj+2,
aj+1, bj
j < 7. (All subscripts are treated modulo 7.

whose 28 vertices
the edges aj
cj
Vertices a0, . . . , a6 form the “outer ring” of the illustration.)

aj , bj , cj, dj
dj, cj

−−−
cj+3, for 0

≤
dj , aj

|
−−−

{
dj, bj

}
−−−

j < 7

−−−

−−−

−−−

≤

0

a) Determine its automorphisms, by ﬁnding a Sims table as in
Section 7.2.1.2. (Use the ordering (a6, b6, c6, d6, . . . , a0, b0,
c0, d0); thus, for example, the permutations of Sn
2 = S26
will ﬁx the ﬁnal vertex d0.) Hint: There will be a surprise!

−

b) Show that it is a vertex-transitive graph: Given any vertices v and v(cid:2), there’s an

automorphism that takes v

v(cid:2). (“All vertices are alike.”)

(cid:4)→
c) Show that it’s also an edge-transitive graph: Given any edges u

there’s an automorphism that takes

u, v
d) Furthermore, it’s a hypohamiltonian graph: It has no Hamiltonian cycle, yet it

into

{

}

{

}

u(cid:2), v(cid:2)

−−−
. (“All edges are alike.”)

−−−

v and u(cid:2)

v(cid:2),

does become Hamiltonian when any vertex is removed.

(cid:3) 100. [HM30 ] Analyze the cycle covers of the ﬂower snark graph Jq, for q > 2 (see

exercise 7.2.2.2–176). How many of them have exactly k cycles?

(cid:3) 103. [M25 ] If a graph G has a Hamiltonian cycle H, show that there’s a very easy

way to test whether or not G is planar. Hint: See Algorithm 7B.

December 4, 2025

(cid:12)
complete graph
Kn
complete bipartite graph
Km,n
Kl,m,n
tripartite graph, complete
10 knight graph
3
×
MATE
TRIG
ACTIVE
SAVE
memory bounds
unscramble
complete graph Kn
binary
Chv´atal
toughness
disconnected
cutsets: sets of vertices that disconnect a graph
components
complete graph
Kn
Km,n
Petersen graph
rook graph Km Kn
SGB
raman
automorphisms

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

49

105. [M18 ] Exactly how many Hamiltonian cycles are present in (a) the complete
graph Kn? (b) the complete bipartite graph Km,n?

106. [M26 ] Continuing exercise 105, enumerate the Hamiltonian cycles of Kl,m,n.
(cid:3) 108. [24 ] According to the discussion in the text, every Hamiltonian cycle that con-

tains edge

02
21 of the 3

10 knight graph also contains the edge
07
28 or

01
13 .
16
28 must be chosen.

×

a) Given those edges, show that either
b) And if that choice is
03
22 leads to a contradiction.
c) Continuing (b), show that edge
d) Continuing (c), consider the consequences of now choosing

16
28 , another edge is forced.

03
15 .

109. [15 ] After Algorithm H deduces the starting pattern
×
knight graph, what are the values of MATE(0), MATE(1), MATE(2), MATE(3), MATE(4)?

for the 3

10

111. [23 ] How much space should be allocated for the arrays TRIG, ACTIVE, and SAVE
in Algorithm H so that no memory bounds will be exceeded?

(cid:3) 112. [26 ] Exactly what changes to the data structures should be made in step H8 of
Algorithm H when we have (a) MATE(u) < 0 and MATE(w) < 0? (b) MATE(u) < 0 and
MATE(w)
0?

0 and MATE(w) < 0? (d) MATE(u)

0? (c) MATE(u)

0 and MATE(w)

≥

≥

≥

≥

113. [20 ] Design an algorithm to “unscramble” the cycle deﬁned by arrays EU and EV
in step H13: It should ﬁnd a permutation such that v1

v1.

vn

v2

−−−

−−−· · · −−−

−−−

115. [M23 ] Describe the search tree of Algorithm H when G is the complete graph Kn.

116. [20 ] Find a Hamiltonian cycle in the graph binary(4, 4, 0) (see Table 7.2.1.6–3).

117. [M22 ] (V. Chv´atal, 1973.) The toughness t(G) of graph G is min
U ),
|
where the minimum is taken over all sets of vertices U such that G
U is disconnected,
and k denotes the number of components. (If G is the complete graph Kn, no set U
disconnects it, and we have t(Kn) =

.) We say that G is “tough” if t(G)

/k(G

1.

U

\

\

|

∞

≥

a) True or false: t(G) = 0 if and only if G isn’t connected.
b) Show that t(G
c) Prove that every Hamiltonian graph is tough.
d) Evaluate t(Km,n) when m
e) What’s t(G) when G is the Petersen graph (which isn’t Hamiltonian)?

t(G) for all edges e.

n.

e)

≤

≤

\

118. [M27 ] Continuing exercise 117, determine t(Km Kn), when m, n > 1.

119. [M24 ] Read the SGB source code of raman and explain the edges of graph E.

120. [M27 ] Let G0 be the graph with vertices
and the following 24 edges: i
i; u
x
u
v
−−−
x
Z, z

U
Y, y

−−−
−−−

−−−
X.

−−−
V

−−−
y

−−−

X

k

j

i

{
−−−
Y

−−−
−−−

i, j, k, u, v, w, x, y, z, U, V, W, X, Y, Z

U , v
w

j
−−−
W

V , w
z

k
−−−
Z

−−−
−−−

}
W;
u;

−−−
−−−

−−−

−−−

−−−

−−−
−−−

−−−
−−−
a) Prove that G0 has twelve automorphisms and exactly two Hamiltonian cycles.
b) Let (p1, p2, p3) = (i, j, k); (q1, q2, q3) = (u, v, w); (Q1, Q2, Q3) = (U, V, W ); and
(t)
(P1, P2, P3) = (Z, X, Y ). For 1
0 be a copy of G0 with vertices
(t)
(t)
1 and then doing this:
to Gt
i
0
−
(t)
(i) remove vertex qt; (ii) remove the edges qt
; (iii) replace
Qt and x
−−−
(t)
the edges pt
; (iv) add edges from
X
qt and Pt
Qt to all the vertices of G
. (Graph Gt therefore has 15+14t
vertices and 24 + 34t edges.) Prove that Gt has exactly two Hamiltonian cycles.

. Obtain graph Gt by appending G

qt by pt
(t)
−−−
(t)
0 except i

−−−
and Pt
(t)

3, let G

, . . . , Z

−−−
, j

−−−

−−−

−−−

x
(t)

, k

X

≤

≤

(t)

(t)

(t)

t

December 4, 2025

50

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

−

1 in preorder, and let C be the cycle x0

C is a Halin graph. (ii) Let C be a regular q-gon with vertices 0, 1, . . . , q

(cid:3) 122. [M27 ] A Halin graph can be deﬁned in two complementary ways: (i) Let T be a
tree in which no node has degree 1, and the root has degree
3. Let the leaves of T be
x0x1 . . . xq
x1
x0. Then
H = T
1.
be nonintersecting chords of C; they partition the interior
i1
Let
of C into t + 1 regions. Let H be the graph of order q + t + 1 whose vertices are the sides
of C, together with those regions. Two sides are adjacent in H if they are consecutive;
a region is adjacent to the sides on its boundary and to the regions with which it shares
a boundary. Then H is a Halin graph. Notice that, under either deﬁnition, a Halin
graph must be planar, and each of its vertices must have degree 3 or more.

j1, . . . , it

−−− · · · −−−

∪
−−−

−−−

−−−

−−−

xq

≥

−

jt

}

{

−

1

For example, here are structures that respectively illustrate (i) and (ii) with q = 7:

0

b

e

f

g

k

a

c

l

d

h

i

j

G

6

H

F

5

E

4

K

I

D

A

1

J

B

2

C

L

3

Halin graph
preorder
regular q-gon
nonintersecting chords
chords
planar
isomorphic
uniformly Hamiltonian
Hamiltonian, uniformly
nonintersecting chords
pi, as random source
regular 100-gon
Halin graphs
Hamiltonian path
articulation point
planar
MRV heuristic
branching
benchmarks
current graph
visible vertices

a) Prove that the corresponding graphs are isomorphic, by ﬁnding a correspondence
that preserves adjacency.

between vertices

and vertices

a, b, . . . , l

A, B, . . . , L

{

}

{

}

+

+

b) If H satisﬁes deﬁnition (i), prove that it also satisﬁes deﬁnition (ii).
c) If H satisﬁes deﬁnition (ii), prove that it also satisﬁes deﬁnition (i).
123. [M30 ] How many nonisomorphic Halin graphs have n vertices, for n
124. [M25 ] A graph is uniformly Hamiltonian if,
Hamiltonian cycle C
with e
Prove that every Halin graph is uniformly Hamiltonian.
125. [20 ] Use the decimal digits (π0.π1π2 . . . )10 of π to deﬁne t nonintersecting chords
(i1
t < 98, by letting ik = π4rπ4r+1
and jk = π4r+2π4r+3, where r is as small as possible with respect to previous chords.
84,
For example, the sequence begins (31
41.
62
These chords deﬁne Halin graphs H

as well as a Hamiltonian cycle C − with e /
∈

93, 23
83, because that one overlaps 31

1000?
it contains a
C −.

64, . . . ); the next chord cannot be 33

jt) of a regular 100-gon for 0

for every edge e,

j1, . . . , it

(t)
π with 101 + t vertices, by exercise 122.
j97?

What is the ﬁnal chord, i97

−−−
−−−

41, 59

26, 53

58, 97

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

≤

≤

C

∈

−−−

127. [20 ] There’s obviously no Hamiltonian path in the graph 7.1.4–(133) from ME to
any of the other states of New England (NH, VT, MA, CT, RI), because NY is an articulation
point. Is there a Hamiltonian path from ME to every other state?
(cid:3) 128. [20 ] Which of the 14 benchmark graphs in Table 1 are planar?
(cid:3) 129. [24 ] The MRV heuristic used in step H11 to choose a vertex for branching prefers
small degree d, because the search tree has a d-way branch. On the other hand, one
can argue that large d is actually good, because step H12 removes d edges — and that
might force a contradiction, or it might cause more vertices to become clothed.

Experiment with a modiﬁed step H11, which maximizes d in cases where d < 2

is impossible, by testing the modiﬁed algorithm on the benchmarks of Table 1.
130. [20 ] At the beginning of step H11, deﬁne the “current graph” G(cid:2) to be the graph
whose vertices are the currently visible vertices, and whose edges are (i) the edges of G
MATE(v) for all outer vertices v.
that haven’t been deleted, and (ii) the edges v
Prove that we could safely jump to step H14 if G(cid:2) isn’t Hamiltonian.

−−−

December 4, 2025

diagonal symmetry
vertical symmetry
axial symmetry
Centrally symmetric
giraﬀe tours
symmetric under 90◦ rotation
path diagrams
knight’s tour
bunch
top-bottom reﬂection
left-right reﬂection
transpose
Ratn¯akara
canonical bunch
bunch
Burnside’s Lemma
canonical bunches
giraﬀe’s tour

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

51

133. [M20 ] Can a knight’s cycle on an n

n board have diagonal symmetry?

×

134. [M20 ] Continuing exercise 133, show that a knight’s cycle on an m
can have vertical symmetry only if m/2 and n are odd. (We require (i, j)
be an edge of the cycle if and only if (m

n board
×
(i(cid:2), j(cid:2)) to
−−−
i(cid:2), j(cid:2)) is also an edge.)

i, j)

(m

1

1

−

−

−−−

−

−

135. [22 ] Given m and n, with m/2 and n odd, construct a graph whose Hamiltonian
cycles correspond to the vertically symmetric m

n knight’s cycles.

×

n knight’s cycles can be surprisingly subtle:

(cid:3) 136. [23 ] Centrally symmetric m

×

(cid:9)(cid:27)(cid:4)

(cid:9)o(cid:5)

(cid:9)9(cid:4)

(cid:9)(cid:27)(cid:4)

(cid:9)(cid:27)1

(cid:9)(cid:29)(cid:23)

(cid:9)(cid:29)(cid:8)

(cid:9)q$

(cid:0)(cid:24)$

(cid:9)r%

(cid:3)s$

(cid:3)q$

>B(cid:23)

(cid:3)B(cid:8)

(cid:9)t$

(cid:3)[$

(cid:9)62

(cid:9)uC

(cid:9)Ob

(cid:3)O(cid:23)

(cid:3)6(cid:8)

(cid:9)E(cid:31)

(cid:8)(cid:28)(cid:5)

(cid:3)(cid:28)(cid:4)

(cid:9)(cid:27)C

(cid:9)EC

(cid:9)_(cid:23)

(cid:3)(cid:29)(cid:8)

(cid:9)vV

(cid:8)v0

(cid:0)r0

(cid:3)x$

(cid:8)qV

(cid:9)jw

(cid:3)r(cid:8)

(cid:9)tV

(cid:9)t$

(cid:9)u2

(cid:9)u$

(cid:9)Ǳb

(cid:9)Z2

(cid:9)u(cid:8)

1 40 11 36 25 38 27
12 9 42 39 28 35 24
41 2 13 10 37 26 29
8 5 16 31 34 23 20
3 14 7 18 21 30 33
6 17 4 15 32 19 22

(cid:9)(cid:27)(cid:4)

(cid:9)o(cid:11)

(cid:9)9(cid:4)

(cid:9)x(cid:4)

(cid:9)(cid:10)1

(cid:9)(cid:29)(cid:23)

(cid:9)](cid:8)

(cid:9)q$

(cid:0)/$

(cid:9)rF

(cid:3)s$

(cid:9)z$

.{(cid:23)

(cid:3)6(cid:8)

(cid:9)t$

(cid:3)[(cid:4)

(cid:9)}F

(cid:9)JC

(cid:9)~V

(cid:9)X(cid:23)

(cid:3)B(cid:8)

(cid:9)E(cid:5)

(cid:8)(cid:28)F

(cid:9)/$

(cid:9)9(cid:4)

(cid:9)}C

(cid:9)c(cid:23)

(cid:3)](cid:8)

(cid:9)v$

(cid:8)q1

(cid:0)r0

(cid:9)gF

(cid:8)zb

(cid:9)~7

(cid:3){(cid:8)

(cid:9)tb

(cid:9)U$

(cid:9)uF

(cid:9)(cid:127)$

(cid:9)JV

(cid:9)j2

(cid:9)l(cid:8)

7 4 19 16 33 2 31
20 15 6 3 30 17 34
5 8 21 18 1 32 29
14 11 42 25 22 35 38
9 26 13 40 37 28 23
12 41 10 27 24 39 36

|

|

1

=

−

19

40

22

On the left, the symmetry shows up because the step numbers of opposite cells always
diﬀer by 21:
7
−
tour begins in one corner, travels to the opposite corner in 21 steps, then repeats its
motions — but rotated 180◦.) The symmetry on the right, however, is quite diﬀerent,
although most of the edges are the same: The step numbers of opposite cells now sum
to 43: 7+36 = 4+39 = 19+24 =
= 29+14 = 43. (It has to be seen to be believed!)
After the right-hand tour has gone halfway, it moves backwards over the paired cells.

(This 6

= 21.

· · ·

· · ·

11

32

29

−

=

=

=

−

×

8

|

|

|

|

|

|

Given m and n, with m even and n odd, construct a graph whose Hamiltonian cy-
n knight’s cycles. Hint: See exercise 135.

cles correspond to the centrally symmetric m

(cid:3) 137. [28 ] Continuing exercise 136, show that centrally symmetric m

n knight’s cycles
are even more subtle when m and n are both even. How can all of them be found, with
the help of a suitable graph G? Explore the case m = n = 8 in detail.

×

×

×

×

138. [24 ] Use the results of exercises 134–137 to compute the exact number of sym-
metrical m

n knight’s cycles, when m mod 4 = 2, n is odd, and mn < 100.

×
139. [21 ] Find all the 10

10 giraﬀe tours that are symmetric under 90◦ rotation.

141. [16 ] Exactly how many 8

8 arrays like (9) deﬁne a closed knight’s tour?

142. [M22 ] If C is a closed knight’s tour in bunch α1α2α3α4, what bunch contains
(a) C’s top-bottom reﬂection? (b) C’s left-right reﬂection? (c) C’s transpose?

143. [16 ] What bunch contains the closed knight’s tour formed from Ratn¯akara’s half-
tour (2)? What is its canonical bunch?

144. [12 ] True or false: abAB is a canonical bunch of multiplicity 4.

145. [15 ] Why can’t ‘a’ appear in the name of a closed knight’s tour’s bunch?

146. [20 ] List all canonical bunches whose multiplicity is 2.

148. [M21 ] Use “Burnside’s Lemma” to determine the number of canonical bunches.

(cid:3) 149. [25 ] Explain how to visit every closed giraﬀe’s tour on a 10

10 board.

33, 34, 43, 44

151. [25 ] The knight’s census described in the text is based on the wedges formed at
8 board, where ij denotes the cell in row i and column j
cells
for 0
i, j < 8. Explain how to carry out a similar census, based instead on the wedges
formed at

03, 04, 30, 37, 40, 47, 73, 74

of an 8

{
≤

×

}

.

(cid:3) 152. [25 ] Do exercise 151, but with the wedges formed at

{

}

12, 15, 21, 26, 51, 56, 62, 65

.

}

{

×

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
1
m
(cid:13)
(cid:14)
(cid:15)
(cid:16)
n
(cid:0)
(cid:8)
(cid:25)
(cid:19)
(cid:6)
p
(cid:16)
(cid:26)
(cid:2)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:25)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:12)
(cid:19)
(cid:13)
p
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:13)
(cid:20)
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
%
P
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
1
(cid:12)
&
’
(
)
(cid:14)
*
W
(cid:15)
R
L
(cid:17)
>
0
(cid:25)
(cid:19)
2
f
A
+
(cid:16)
(cid:26)
(cid:0)
(cid:2)
&
2
8
A
!
,
5
(cid:0)
(cid:7)
%
P
&
(
;
8
*
+
"
,
4
5
(cid:7)
(cid:31)
(cid:12)
&
=
(
;
)
(cid:14)
3
W
"
R
-
(cid:26)
=
(cid:13)
A
:
M
(cid:0)
(cid:7)
(cid:9)
(cid:7)
C
F
(cid:31)
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
’
K
(cid:13)
*
W
L
M
(cid:0)
(cid:7)
(cid:23)
2
(cid:13)
A
W
(cid:0)
(cid:7)
(cid:3)
G
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:31)
G
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:31)
’
G
;
W
"
:
M
(cid:2)
(cid:7)
(cid:8)
=
(cid:13)
A
:
M
(cid:0)
(cid:7)
(cid:9)
(cid:7)
C
P
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
m
’

(cid:13)
(cid:14)
"
(cid:16)
:
(cid:26)
M
(cid:23)
’
(cid:6)
(cid:13)
:
M
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:25)
(cid:14)
(cid:16)
(cid:26)
(cid:0)
(cid:2)
(cid:8)
(cid:31)
(cid:11)
(cid:25)

(cid:14)
\
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
’
(cid:13)
(cid:20)
:
M
(cid:0)
(cid:8)
(cid:9)
(cid:7)
C
P
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
0
P
1
(cid:25)
’
;
(cid:14)
‘
H
(cid:16)
:
(cid:17)
M
(cid:2)
1
(cid:25)
w
=
8
p
A
!
(cid:15)
I
:
(cid:17)
>
(cid:4)
w
8
(cid:20)
!
,
5
(cid:0)
(cid:8)
F
(cid:4)
(cid:25)
&
8
(cid:14)
W
I
(cid:26)
5
(cid:0)
0
(cid:31)
1
(cid:25)
2
(
;
(cid:14)
i
‘
\
(cid:16)
4
n
(cid:2)
=
8
(cid:20)
A
,
:
>
(cid:0)
(cid:9)
(cid:7)
C
F
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
F
(
*
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
K
3
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
G
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
F
G
W
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(
3
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
G
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
1
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:25)
(cid:19)
(cid:6)
f
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
y
(cid:25)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
n
(cid:2)
(cid:8)
m
(cid:19)
(cid:13)
f
(cid:15)
(cid:16)
n
(cid:0)
(cid:8)
(cid:19)
(cid:13)
(cid:20)
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:30)
D
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
F
1
m
&
’
(
a
(cid:14)
*
W
(cid:15)
I
-
n
.
0
(cid:19)
2
(
(cid:20)
i
+
4
(cid:0)
(cid:2)
(cid:3)
&
2
8
A
,
5
(cid:0)
(cid:7)
(cid:30)
D
1
(
;
*
‘
\
4
(cid:21)
(cid:2)
(cid:7)
(cid:31)
(cid:25)
7
@
(
;
8
f
i
W
"
R
L
(cid:26)
@
(cid:13)
A
:
M
(cid:0)
(cid:7)
(cid:9)
(cid:7)
C
F
(cid:31)
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
’
|
(cid:13)
*
W
-
M
(cid:0)
(cid:7)
2
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
1
(cid:25)
G
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(
(cid:20)
*
4
(cid:0)
(cid:2)
(cid:3)
(cid:31)
G
;
W
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:13)
A
:
M
(cid:0)
(cid:7)
(cid:9)
(cid:7)
C
D
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
’
(cid:6)
(cid:13)
(cid:14)
(cid:16)
:
(cid:26)
M
1
(cid:23)
(cid:13)
(cid:15)
(cid:21)
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:19)
(
(cid:6)
(cid:20)
*
W
4
(cid:2)
(cid:3)
2
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:31)
y
(cid:25)
^
(cid:14)
H
(cid:16)
n
(cid:2)
(cid:8)
(cid:19)
’
(cid:13)
(cid:20)
:
M
(cid:0)
(cid:8)
(cid:9)
(cid:7)
C
D
;
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:30)
D
1
(cid:25)
’
;
(cid:14)
‘
\
(cid:16)
:
n
M
(cid:2)
(cid:25)
7
@
(
8
f
i
(cid:15)
R
L
n
.
(cid:4)
(cid:19)
(cid:20)
!
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:4)
1
(cid:25)
&
8
(cid:14)
(cid:15)
I
(cid:17)
5
(cid:0)
0
(cid:31)
1
(cid:25)
(cid:19)
(
;
f
*
+
H
(cid:16)
4
(cid:17)
(cid:2)
@
8
(cid:20)
A
,
:
.
(cid:0)
(cid:9)
(cid:7)
C
F
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
F
(
*
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
|
i
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
F
K
*
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
(
i
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
G
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
topological types
al-‘Adl¯ı
knight graph
equivalence classes
rotation and/or reﬂection
census
diverse knight’s tours
Jelliss
angles of a knight move
tarnished
1:3 cuts
1:2 cuts
X cuts
self-intersections
Perpendicular cuts
conjugate

52

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

154. [19 ] To which of the thirteen topological types in Fig. 124 does al-‘Adl¯ı’s classic
tour (1) belong? Hint: See (9).

155. [25 ] The classiﬁcation of knight’s cycles in Fig. 124 applies only to square boards.
Show that additional topological types arise on m

n boards when m < n.

×

156. [24 ] Compute the exact numbers of 8

8 knight’s cycles of each type in Fig. 124.
(cid:3) 157. [24 ] The set of all knight moves on a chessboard — that is, the set of all edges on
the 8
8 knight graph — is partitioned into 21 equivalence classes of size 8, when we
say that two edges are equivalent if rotation and/or reﬂection takes one into the other.
Each move can therefore be given a label from A to U, indicating its class:

×

×

A B C D E F
G H I J K L
M N O P Q R
S T U U T S
R Q P O N M
L K J I H G
F E D C B A

A
B
C
D
E
F

G
H
I
J
K
L

M
N
O
P
Q
R

S
T
U
U
T
S

R
Q
P
O
N
M

L
K
J
I
H
G

F
E
D
C
B
A

F
E
D
C
B
A

L
K
J
I
H
G

R
Q
P
O
N
M

S
T
U
U
T
S

M
N
O
P
Q
R

G
H
I
J
K
L

A
B
C
D
E
F

F E D C B A
L K J I H G
R Q P O N M
S T U U T S
M N O P Q R
G H I J K L
A B C D E F

8 knight’s cycles (a) have at least one move
Use a census to determine how many 8
of each class; (b) have at least two moves of each class; (c) have all eight of the moves
in six diﬀerent classes. (Every cycle contains all eight of the class A moves.)

×

(cid:3) 158. [29 ] (G. P. Jelliss, 1976.) According to Fig. 123, six diﬀerent angles

θ, 90◦,
90◦+θ, 180◦
can occur in a wedge. For every such angle α, determine the
maximum and minimum number of times α can occur among the 64 moves of a
closed knight’s tour. Determine also the maximum and minimum sum of all 64 angles.
Furthermore, discover exactly how many tours achieve those maxima and minima.

θ, 180◦

θ, 90◦

−

−

}

{

159. [34 ] Every knight’s move “tarnishes” the two cells that it jumps over, by invading
their space. A corner call cannot be tarnished; and the other 24 cells on the border of a
chessboard can be tarnished at most twice. The 36 interior cells can each be tarnished
at most seven times (not eight!).

Use a census to discover as many interesting facts as you can about the multisets

of 128 tarnishments that can arise in closed tours.

’; (ii) 1:3 cuts, ‘

’; (iii) 1:2 cuts, ‘

160. [39 ] Knight moves can intersect each other in essentially four ways: (i) perpen-
dicular, ‘
’, also called
X cuts. Perpendicular cuts are asymmetrical, with one arm having a cut ratio of 3:2
while the ratio in the other is 1:4. The other types are symmetrical, having the stated
cut ratios; the angles at the crossing point are θ and 180◦
θ for
(ii) and (iv). Notice that every knight move has exactly one “conjugate,” with which it
. What interesting facts about intersections can you turn up, censuswise?
makes an
(cid:3) 163. [40 ] Closed tours can also be depicted by changing color when the path is crossed:

’; and (iv) 1:1 cuts, ‘

θ for (iii), but 90◦

−

±

(i)

(ii)

(iii)

(iv)

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

53

In such harlequinesque patterns, we cross the knight’s path an odd number of times
when we travel from a shaded region to the edge of the board. (Graphic designers know
this as the “eoﬁll” operation, short for “even-odd ﬁlling.”)

Examples (i) and (ii) are the 6
547
60

303
20 = 15.15, out of the total conceivable area of 5

6 tours with minimum and maximum shaded
5 = 25.

area,
(The extremal tours that achieve those limits are in fact unique, up to symmetry.)

9.11667 and

×

≈

×

Suppose C is an oriented cycle that divides the plane into regions when it crosses
itself. The winding number of a point p with respect to C, when p /
C, is the net
∈
number of times by which C encircles p in the counterclockwise direction. All points
of a region have the same winding number. The shaded area of C is the sum of the
areas of regions whose winding number is odd.

harlequinesque patterns
eoﬁll
even-odd ﬁlling
winding number
swept area
swept area
Parmentier
Hamilton’s graph
1-conﬁgs
m-conﬁgs
dodecahedron graph
m-classes
involution
marked involution
recurrence relation

}

{

3,

2,

1,

0,

(or

0, 1, 2, 3, 4, 5

The swept area of C is the integral of the winding number over all p /
C;
∈
equivalently, it’s the sum, over all regions, of the area of that region times the winding
number of that region. Example (iii) is a cycle whose regions have winding numbers
, depending on which way we traverse that
{
cycle). It’s the unique cycle whose swept area achieves the maximum value (namely
61); its shaded area is
12.067. On the other hand, the cycle in example (iv) has
≈
.) Among all
a swept area of zero. (Its regions have winding numbers
8

1, 0, 1, 2
}
10.667.
8 knight’s cycles. How large and
small can the shaded area be? What is the maximum swept area? How many of the
49 internal corner points can have winding number zero? And so on.

13 such cycles, it uniquely has the smallest shaded area:

Use a census to explore these aspects of 8

−
181
15

−
≈

2,
32
3

{−

−

−

−

−

×

4,

5

}

·

164. [M30 ] Prove that the swept area A of an m
and it can be computed in at least two ways:

×

n knight’s cycle is always an integer,

a) A is the sum of the winding numbers at the (m
b) A =

i1j0 + i1j2

+ imn

1
2 (i0j1

−
i2j1 +
1jmn
(imn, jmn) = (i0, j0).

· · ·

−

(i0, j0)

(i1, j1)

−

−
−−−· · · −−−

−−−

1)(n

−
imnjmn

1) internal corner points.
1), when the tour is

−

−

165. [22 ] (T. Parmentier, 1891.) Every knight move has four possible slopes, namely
2, +2, and +1/2, as exhibited in exercise 157. Is there a knight’s tour that has

1/2,

−

−
exactly 16 moves of each slope?
170. [20 ] What 14-conﬁgs of Hamilton’s graph (26) belong to class 11¯100?
171. [10 ] How many 1-conﬁgs does a graph have?

172. [M15 ] Describe the (n

1)-conﬁgs of an n-vertex graph.

−

173. [20 ] According to the text, Algorithm E discovers that the dodecahedron graph
(26) has exactly six 16-classes, namely (¯1101, ¯111¯1, 0110, 1001, 101¯1, 1212), of respective
sizes (4, 6, 2, 6, 4, 10). What then are the 17-classes, and their sizes?
174. [15 ] Explain the last step, ‘11¯1

18 C20’, of (32).

(cid:3) 176. [M20 ] An involution is a permutation whose cycles all have length 1 or 2. A
marked involution is similar, but each 1-cycle is either “marked” or “unmarked.” For
example, the marked involutions of order 2 are (1)(2), (1)(2)(cid:2), (1)(cid:2)(2), (1)(cid:2)(2)(cid:2), and (12).
a) Let tn and Tn be the number of involutions and marked involutions of order n.
(The ﬁrst few values are (t0, . . . , t9) = (1, 1, 2, 4, 10, 26, 76, 232, 764, 2620) and
(T0,. . .,T9) = (1,2,5,14,43,142,499,1850,7193,29186).) Show that Tn =
tk.

n
k

k

b) Prove the recurrence relation Tn = 2Tn
c) Suppose q =

Fm

is the number of elements in the extended m-frontier of a

1 + (n

−

1)Tn

−

2, for n

2.

(cid:14)

(cid:15)

(cid:16)

−

≥

graph. Show that the total number of m-classes in that graph is at most Tq.

|

|

(cid:7)

(cid:4)→

December 4, 2025

asymptotic
marked involutions
involutions
MATE table
complete graph
complete graph Kn
frontier
FR
IFR
NBR
traverse
trie
contribute()
MATE table
try(i, j)
basic mate table
BMATE table
Δ
Stanford GraphBase
n knight graph
m
board graphs
contribute()
try(i, j)
lexicographically smallest

×

54

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

177. [HM28 ] Study the asymptotic behavior of Tn, by deriving a formula for marked
involutions that’s analogous to Eq. 5.1.4–(53) for ordinary involutions.
178. [18 ] Why is it wise to use marked involutions, encoded in the form a1 . . . aq, as
class names, instead of using a MATE table directly?
179. [20 ] In a MATE table such as (35), MATE[j] = (
respectively (bare, inner, mated to uk).

1, 0, k > 0) means that uj is

−

a) Convert a given marked involution a1 . . . aq to an equivalent MATE table.
b) Conversely, convert a given MATE table to an equivalent marked involution.

−

−

(cid:7)

∈

1.

(cid:4)→

(cid:4)→

Fm

Fm

181. [20 ] Explain (37) by considering two cases: (i) m+1
183. [20 ] List (by hand) all relations α
184. [M23 ] Find all α such that α
185. [M25 ] Suppose G is the complete graph Kn. What is F (m, r, s, t), the size of
an m-class for which (r, s, 2t) elements of the extended frontier
Fm = (m + 1, . . . , n)
are respectively (inner, bare, outer)? (Here m + r + s + 2t = n.)

m β that are valid for the complete graph K5.

m Cp, when G is the graph Kn and n

1; (ii) m+1 /
∈

(cid:7)
187. [24 ] Give details of how Algorithm E moves from
Fm when it updates
FR, IFR, q0, and q in step E2. Also compute σ and τ for (36)–(38); r and NBR for (39).
189. [20 ] Explain how Algorithm E can traverse its “old” trie in steps E3 and E8.
(cid:3) 191. [21 ] Design a subroutine ‘contribute()’ for use by Algorithm E. It should insert
the m-class deﬁned by the MATE table into the current trie of m-classes, if that class
(cid:0) ] to that class’s current size.
isn’t already present in the trie; and it should add OWT[p(cid:2)q
Note: As stated in step E2, the trie has p nodes and w lieves.

(cid:7)
p.

1 to

Fm

≥

(cid:7)

(cid:7)

−

(cid:3) 192. [M20 ] True or false: If OMATE[1] > 0 in step E4, then BMATE[OMATE[1]σ] = 0.
(cid:3) 193. [30 ] Design a subroutine ‘try(i, j)’ for use by Algorithm E. It should contribute()
if we can legitimately connect ui with uj within each m-conﬁg in the class of the BMATE
table. It should also update CYC[m(cid:2)], if that connection would close a suitable m(cid:2)-cycle.
32 knight graph?
196. [20 ] When the cells of a chessboard are ordered columnwise as in (41), the ﬁrst
26 cells make a curious sub-board, which consists of two rows of length 4 above six
rows of length 3. Find, by hand, a knight’s cycle on that sub-board.

(cid:3) 195. [20 ] How large should Δ be, when Algorithm E works on the 8

×

(cid:3) 197. [20 ] If you use the Stanford GraphBase to create the 8

32 knight graph for

Algorithm E, should you make board (8, 32, 0, 0, 5, 0, 0) or board (32, 8, 0, 0, 5, 0, 0)?
198. [24 ] Watching Algorithm E, answer the following about the computation of (40):
a) Every m-class enters its trie via the contribute() subroutine of exercise 191. Some
classes are contributed once; others are contributed many times. How often was
240?
that subroutine called, as a function of m mod 8, assuming that 72 < m
b) Continuing (a), how often did the subroutine try(i, j) of exercise 193 update

≤

CYC[m(cid:2)] instead of calling contribute()?

c) What is the smallest weight of an m-class when (i) m = 32? (ii) m = 64?

(iii) m = 96? (iv) m = 128?

×

d) What is the largest weight of an m-class, for those m?
e) What’s the largest m for which some m-class has weight 1?
f) What’s the smallest m for which some m-class has weight
g) What is the lexicographically smallest (72 + r)-class, for 0

9

10
?
r < 8?

≥
≤

200. [23 ] Consider the eight transitions in the cycle (42). What will α1, α2, . . . , α7
be, when (a) α0 = 1234214300000000? (b) α0 = 01¯12314505004023?

December 4, 2025

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

55

201. [21 ] What 8-classes a1 . . . a16 of the 8

32 knight graph have a1, . . . , a16 > 0?
(cid:3) 202. [25 ] Construct a periodic knight’s tour, analogous to those of (43), in which the

×

knight changes direction sixteen times as it traverses the cycle.

(cid:3) 204. [25 ] Notice that the trie in Fig. 125 can be reconstructed by just knowing the
null-versus-nonnull patterns of the node ﬁelds: Writing 0 for a null link and 1 otherwise,
the root’s pattern is 1110, and its leftmost child’s pattern is 0010, and so on; the
patterns in preorder are 1110, 0010, 0110, 0010, 1000, 0010, 0010, 0100, 0101, 0110,
0010, 1000, 0010, 0001. From these patterns, we can deduce the names of all six lieves,
and we can visit the lieves in lexicographic order — needing no link ﬁelds whatsoever!
(See Theorem 2.3.1A.) In particular, the space needed in Algorithm E’s OMEM for the
calculation of (40) can be reduced from 40 bytes per node to just 10 bits per node.
What revisions to Algorithm E will exploit this compression scheme?

205. [20 ] Let G be the Petersen graph, GP(5, 2) in the notation of exercise 11, with
its vertices arranged in the order (0, 1, 2, 3, 4, 0(cid:2), 1(cid:2), 2(cid:2), 3(cid:2), 4(cid:2)). How many m-cycles
and m-paths of G are found by (a) Algorithm E? (b) Algorithm E

?

+

(cid:3) 206. [21 ] The text observes that 256 gigabytes of RAM were needed for the compu-

tation of (40). Discuss the memory requirements for computing (44).

periodic knight’s tour
preorder
trie, compressed
compression
Petersen graph
RAM
memory, random access
octabyte
data structures
RAM
Hamiltonian paths
induced graph
graph of knight moves
generating function
open
tournament
football scores
Stanford GraphBase

(cid:3) 207. [30 ] When a trie with P nodes is implemented as in Fig. 125, every node contains
, each of those ﬁelds

Δ link ﬁelds that hold integers in [0 . . P ]. Therefore, if P > 2
must have more than 32 bits (and will typically be an octabyte with 64 bits).

32

Suppose P

2

. Devise a way to represent P -node tries whose link ﬁelds ﬁt in

32 bits, thereby needing only about half as much RAM. Hint: Use randomization.

35

≈

209. [26 ] Design Algorithm E
numbers PATH[m] for 2
in the induced graph G

m
≤
1, . . . , m

+

≤
| {

, a modiﬁcation of Algorithm E that computes the
n, where PATH[m] is the number of Hamiltonian paths

and G is a given graph on vertices

1, . . . , n

.

}

{
210. [HM46 ] Let Sm,n be the number of closed m
n knight’s tours, namely the
n board; and
number of Hamiltonian cycles in the graph of knight moves on an m
let Sm(z) =
be the corresponding generating function for boards with
m rows. The periodic nature of Algorithm E proves that Sm(z) = Pm(z)/Qm(z) for
certain (huge) relatively prime polynomials Pm(z) and Qm(z).

0 Sm,nz

(cid:14)

×

×

}

≥

n

n

Similarly, if S

+
m,n is the number of open m
+
Hamiltonian paths), with generating function S
m(z) =
+
+
+
nature of Algorithm E
m(z).
shows that S
m (z)/Q
m(z) = P
(cid:14)
3
m
+
(z)
m(z) is a multiple of Q

Prove or disprove that Q

×

+

n knight’s tours (the number of
, the periodic

+
m,nz

0 S

n

n

≥

when m

5.

≥

211. [18 ] What is the other Hamiltonian cycle of the digraph (47)?

212. [21 ] The digraph (47) is an example of a tournament (an orientation of Kn).
True or false: Any tournament for which no vertex has in-degree 0 or out-degree 0 has
a Hamiltonian cycle.

8 matrix (46) is just part of a 120

213. [35 ] The 8
120 matrix in the Stanford
GraphBase, which contains all of the scores of the American 1990 college football
season. When the full matrix is converted to a digraph on 120 vertices, there clearly is
no Hamiltonian cycle — because, for example, Fullerton won no games.

×

×

We do get a plausible digraph if we include two-way arcs for the close games, by
saying that u
v also when the diﬀerence between their scores is less than 10. (For
example, (47) would gain 11 more arcs: Brown → Princeton, Brown → Yale, Columbia →
Harvard, Cornell → Dartmouth, Harvard → Cornell, Harvard → Penn, Penn → Brown,

−−→

December 4, 2025

56

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

Penn → Cornell, Princeton → Columbia, Princeton → Cornell, Princeton → Harvard.) The
resulting digraph, football-tol10.gb, is available online.

Prove that football-tol10.gb has a Hamiltonian path but no Hamiltonian cycle.
215. [21 ] One of many interesting ways to orient the edges of the n-cube, illustrated
for n = 4 in (48),
w, where v = v1 . . . vn and w =
−−→
v1 . . . vj
1 ¯vj vj+1 . . . vn is the same as v but with the jth component complemented,
if and only if v either has even parity (that is, v1 +
+ vn is even) and j is even, or
v has odd parity and j is odd.

is the following: Let v

· · ·

−

Use Algorithm B to enumerate the Hamiltonian cycles for this orientation when

n = 5. How does this compare to the undirected case (graph Q in Table 1)?
216. [M20 ] Another orientation of the n-cube stipulates that v
v either has even parity and j = k, or v has odd parity and j

−−→

= k, where k is ﬁxed.

w if and only if

Prove that the number of 2

-cycles with this orientation is exactly twice the

n

number of 2

-cycles in the unoriented (n

1)-cube.

n

1

−

−

(cid:3) 217. [21 ] Consider the graph Πn whose vertices are the n! permutations of

,
}
w connect permutations that diﬀer by interchanging adjacent

1, . . . , n

{

and whose edges v
elements: v = v1 . . . vn and w = v1 . . . vj

−−−

1vj+1vj vj+2 . . . vn for some j, 1

−

j < n.

As in exercise 215, we can orient Πn by letting v

w if and only if v either is

≤

an even permutation and j is even, or v is an odd permutation and j is odd.
Find, by hand, a Hamiltonian cycle of Π4 with this orientation.

−−→

online
orient the edges
n-cube
parity
permutations
Stappers
Chess moves
bishop
king
knight
queen
rook
unique cycle
Shift and save or bump
SB(m, n)
m-ary strings
self-loops

218. [27 ] Continuing exercises 216 and 217, we can also orient Πn by letting v
when v either is even and j = k, or v is odd and j

= k, for ﬁxed k.

w

−−→

a) Prove by hand that Π4 has no Hamiltonian cycle with this orientation when k = 1.
b) Find by computer the number of Hamiltonian cycles of Π5 when k is (i) 1; (ii) 2.
220. [32 ] (F. Stappers, 2025.) Chess moves lead to interesting digraphs in yet another
way: Place either a bishop (B), king (K), knight (N), queen (Q), or rook (R) on each
cell of a board, and create a cycle where (i) every piece can capture its successor; and
(ii) no piece captures a piece of the same kind.

Consider, for example, the following three placements on a 5

5 board:

B00 K01 N02 Q03 R04
K10 N11 Q12 R13 B14
N20 Q21 R22 B23 K24
Q30 R31 B32 K33 N34
R40 B41 K42 N43 Q44

;

B00 R01 B02 Q03 B04
R10 B11 N12 B13 Q14
R20 N21 K22 N23 Q24
R30 N31 K32 N33 Q34
R40 K41 K42 K43 Q44

;

×
B00 N01 Q02 N03 Q04
B10 N11 Q12 N13 R14
K20 K21 R22 Q23 R24
Q30 K31 R32 R33 B34
K40 K41 B42 B43 N44

.

The ﬁrst example yields 2,016,000 cycles, and (B00 K33 B23 K01 N02 B14 Q03 N43 K24 N34
K42 R31 N11 B32 Q21 R22 Q12 R13 K10 N20 B41 Q30 R40 Q44 R04 B00) is lexicographically least.

a) Find one of the 29201 cycles for the middle example.
b) Can you ﬁnd the unique cycle for the rightmost example?

221. [22 ] Continuing the previous exercise, construct (by hand) a 4
4 placement
that (i) uses each of the ﬁve allowable pieces at least once, and (ii) has a unique cycle.
(cid:3) 223. [28 ] (Shift and save or bump.) Let SB(m, n) be the digraph whose vertices
n and whose arcs
= (x + 1) mod m.

are the m-ary strings x1x2 . . . xn with 0
are x1x2 . . . xn
x2 . . . xnx1, x1x2 . . . xn
(Notice that there are self-loops whenever x1 = x2 =

+
+
≤
≤
1 , where x
= xn.)

xk < m for 1
x2 . . . xnx

≤
−−→

−−→

×

k

a) True or false: Every vertex of SB(m, n) has in-degree 2.
b) Find a connection between the Hamiltonian cycles of SB(m, n) and something

· · ·

else that has been studied in Section 7.2.1.1.

December 4, 2025

(cid:12)
(cid:12)
counterclockwise
pivot point
plumb-line
symmetrical
angular velocity
whirling knight’s tour
coils
whirling king’s tour
symmetries
bidirected path
trail
bidirected graph
complete bidirected graph
extroverted edges

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

57

c) Prove that SB(m, 2) has no Hamiltonian cycles when m > 2.
d) Find a Hamiltonian cycle of SB(3, 3).
e) Let C be a Hamiltonian cycle of SB(m, n). Prove that there’s a set S of m-
x2 . . . xnx1 is in C if and only if

1 such that x1x2 . . . xn

−−→

ary strings y1 . . . yn
x2 . . . xn

S.

−

∈

f) How many Hamiltonian cycles are in SB(m, 3), for 2

m

7?

≤

≤

224. [46 ] Prove or disprove: SB(3, n) has no Hamiltonian cycles when n is even.

225. [46 ] Construct a Hamiltonian cycle in SB(m, 3) for all m > 1.

227. [M20 ] When does a move from cell (i, j) to cell (i(cid:2), j(cid:2)) of a rectangular board
go “counterclockwise” with respect to a given pivot point (p, q)? State the answer as
an algebraic relation in terms of i, j, i(cid:2), j(cid:2), p, and q.

228. [17 ] How can the middle example in (51) be “uniquely steady” (in the sense of
nearly equal distances between plumb-line crossings) when it isn’t symmetrical?

2

1

,

n

×
1

[mn is odd] vertices (i, j) for 0

229. [33 ] An m
digraph: There are mn
m
−
omitting (
2
i(cid:2))
(i
+ (j
pivot point (
a plumb-line above the pivot point exactly c times. Let Wm,n =
W
n whirling knight’s tours with c coils.

n whirling knight’s tour is a Hamiltonian cycle on the following
j < n,
(i(cid:2), j(cid:2)) when we have
= 5 and (i(cid:2), j(cid:2)) is counterclockwise from (i, j) with respect to the
1
2 ), in the sense of exercise 227. The cycle has c coils if it crosses
−
(c)
m,n, where

−
2 ) when mn is odd. The arcs are (i, j)
2

i < m and 0

j(cid:2))
−
1
m
−
,
2

0 W

−−→

−

−

≤

≤

≥

n

c

(c)
m,n is the number of m
a) Can there be a knight move for which neither (i, j)
b) Prove that Wm,n = 0 when n
c) If m
n, prove that W
d) Use Algorithm B to compute W

1.
(c)
m,n = 0 when c < m/2 or c > m.

(c)
m,n for m

−−→

2m

≤

≥

−

×

n

(cid:14)
(i(cid:2), j(cid:2)) nor (i(cid:2), j(cid:2))

(i, j)?

−−→

≤

≤

10 and n/2

c

n.

≤

≤

230. [15 ] True or false: The transpose of a whirling knight’s tour is also a whirling
knight’s tour, when traveled in the opposite direction.

231. [37 ] Find n
(The computations of exercise 229 show that no such tours exist when n < 12.)

n whirling knight’s tours that have exactly (a) n/2 (b) n coils.

×

(cid:3) 232. [30 ] Find inﬁnitely many solutions to problem 231(b).

235. [M30 ] An m
n whirling king’s tour is a Hamiltonian cycle on a digraph like the
one in exercise 229, except that king moves replace knight moves; more precisely, the
j(cid:2))
statement ‘(i
2’. Let Xm,n
(c)
m,n in exercise 229.
and X

(c)
−
m,n count whirling king’s tours, by analogy with Wm,n and W

= 5’ is replaced by ‘1

+ (j

+ (j

j(cid:2))

i(cid:2))

i(cid:2))

−

−

×

≤

−

≤

(i

2

2

2

2

a) Prove that Xn,n > 0 for all n > 1. (When n = 1 there are no vertices!)
b) Furthermore X
c) Furthermore Xm,n = 0 when m is odd and n > m + 1.
d) Furthermore Xm,n = Xm,n

= 0 implies c = c(cid:2).

= 0 and X

2 when n

(c)
m,n

(c
)
m,n

2m.

(cid:0)

−

≥

236. [21 ] Continuing exercise 235, compute Xm,n for m

n

8. Look for symmetries!

240. [05 ] True or false: A bidirected path or cycle is always a trail.

≤

≤

241. [16 ] Construct a bidirected graph that has a trail between u and v but no path.

(cid:3) 242. [M22 ] The “complete bidirected graph” on vertices

vi (cid:4)(cid:5) vj , and vi (cid:5)(cid:4) vj for all i

= j.

v1, . . . , vn

{

}

has vi (cid:4)(cid:4) vj ,

a) How many Hamiltonian (i) paths (ii) cycles does it have?
b) How many does it have if we omit the directed edges?
c) How many does it have if we omit the extroverted edges?

December 4, 2025

(cid:12)
(cid:12)
(cid:12)
fers
alﬁl
digraph
directed graphs
strictly alternating Hamiltonian cycles
whirling
counterclockwise
Stanford GraphBase
digraph, representation of
linked list
arc node
TIP(a)
NEXT(a)
length l
LEN(a)
bidigraph, representation of
LEN ﬁeld
Hamiltonian matching
unscramble

58

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

244. [20 ] Using Algorithm B, determine the number of closed tours on an 8
that alternately make the moves of a knight and (a) a fers; (b) an alﬁl. (See (55).)

×

8 board

245. [17 ] True or false: The graph G(B) in Algorithm B is bipartite

B is directed.
(cid:3) 246. [25 ] Extend the trick of (54) from undirected graphs to directed graphs: Given
any two directed graphs G and H on the same vertices, construct a bidirected graph B
whose Hamiltonian cycles are in one-to-one correspondence with the Hamiltonian cycles
that strictly alternate between arcs of G and arcs of H. (For example, suppose the
(v + 1) mod 10 and the arcs of H
vertices are
(v + 3) mod 10. Then there are two strictly alternating Hamiltonian cycles:
are v
4
1
0
9
6
5

5
4
→
0.) Hint: B can have more vertices than G and H.

and the arcs of G are v

0, 1, . . . , 9

0 and 0

⇐⇒

⇒

→

⇒

→

⇒

→

⇒

⇒

⇒

→

→

⇒

→

⇒

}

7

8

9

2

3

6

{

3

7

8

1

2

⇒
⇒
⇒

→
→

→
→

247. [21 ] Find all of the “whirling” 8
8 cycles that strictly alternate between knight
moves and grid moves (as in (54)), always counterclockwise with respect to the center.

×

250. [22 ] The Stanford GraphBase represents a directed graph by specifying, for each
vertex v, a linked list of the arcs from v to its successor vertices. Every element of
this list is an “arc node,” and each arc node a has ﬁelds TIP(a) and NEXT(a). If the
successors of v are w1, w2, . . . , wd, the list contains arc nodes a1, a2, . . . , ad, where

ARCS(v) = a1, TIP(a1) = w1, NEXT(a1) = a2, TIP(a2) = w2, . . . ,

TIP(ad) = wd, NEXT(ad) = Λ.

(See, for example, 7–(31) and Algorithm 7B, near the beginning of Chapter 7.)

Arc nodes also contain more. For example, there’s a LEN ﬁeld: An arc of length l

from v to w is represented by an arc node with TIP(a) = w and LEN(a) = l.

To represent a bidirected graph, we can use the two low bits of each LEN ﬁeld, by
representing a bidirected edge between v and w as an arc of length l from v to w, where

v (cid:4)(cid:4) w
v (cid:5)(cid:5) w

⇐⇒
⇐⇒

l mod 4 = 3;
l mod 4 = 1;

v (cid:4)(cid:5) w
v (cid:5)(cid:4) w

⇐⇒
⇐⇒

l mod 4 = 2;
l mod 4 = 0.

(Since v (cid:4)(cid:4) w means the same as w (cid:5)(cid:5) v, we could represent that edge also as an arc with
l mod 4 = 1 from w to v. Both arcs could, in fact, be speciﬁed. Note that LEN(a) has
no connection whatsoever with the LEN ﬁeld of Algorithm 7.2.2.1X and its cousins.)

Explain how to initialize the NBR and ADJ arrays in step B1 of Algorithm B, when

the bidirected input graph B is represented in this way.

(cid:3) 251. [25 ] How should the data structures be set up in step B3 of Algorithm B so that

the ﬁrst edge of the partial Hamiltonian matching is CURU

CURV?

252. [22 ] Exactly what changes to the data structures should be made in step B8 of
Algorithm B when we have (a) MATE(u) < 0? (b) MATE(u)

0?

(cid:3) 253. [26 ] When Algorithm B discovers a Hamiltonian matching in step B13, what’s
a good way for it to “unscramble” the corresponding Hamiltonian cycle of the input
graph and to print it in a format like (53)? (Compare with exercise 113.)

−−−

≥

254. [20 ] The text sketches the steps that lead to (60) and the ﬁrst Hamiltonian
matching of (57). What happens next?

256. [21 ] Customize Algorithm B to the special case where the input is simply an
ordinary directed graph, by showing that the answers to exercises 250 and 253 can be
signiﬁcantly simpliﬁed in that case.

December 4, 2025

Hamiltonian path
Hamiltonian paths of a bidigraph
dynamic enumeration
bipartite
exact cover problem
knight graph
step matrix
rotated 180◦
near symmetry
Carpenter
Sierpi´nski gasket graph
meander frieze
frieze
Greek vases
vases
Geometric
Dipylon Amphora
margins
parity
reduced
symmetric

7.2.2.4

HAMILTONIAN PATHS AND CYCLES: EXERCISES

59

(cid:3) 270. [22 ] If G is a digraph on n vertices, deﬁne

G by adding two vertices s and t, with

v and v

2n additional arcs s

t for all v in G; also t
a) Show that G has a Hamiltonian path if and only if
b) Prove that if G has no cycles, it has at most one Hamiltonian path.
c) True or false: Algorithm B will handle

G in linear time when G is acyclic.

−−→
G has a Hamiltonian cycle.

−−→

−−→

s.

(cid:7)

(cid:7)

p

(cid:7)

(m + n)) steps to test whether or not G has a Hamiltonian path.

271. [M25 ] If G is a digraph with m arcs, n vertices, and p cycles, show that we
need at most O(n
272. [22 ] How can Algorithm B be used to visit all Hamiltonian paths of a bidigraph?
275. [41 ] Develop a dynamic enumeration algorithm, analogous to Algorithm E, that
counts the number of Hamiltonian cycles in B
n, when B
is a given bidirected graph on n vertices.
298. [20 ] Given a bipartite graph G with n vertices in each part, construct an exact
+
cover problem with 3n primary items u−, u
, v: two for each vertex u in the ﬁrst part,
and one for each vertex v in the second part. Let the options be ‘u− v w
’, for all
triples with u

1, . . . , m

w and u

for all 1

= w.

| {

m

≤

≤

}

v

+

−−−

−−−

a) What do the solutions to this exact cover problem represent?
b) Experiment with this construction when G is the 6

6 knight graph.

(cid:3) 299. [27 ] How many 8

32 + k occupy the same column, for 1
300. [24 ] Find a knight’s tour whose step matrix has

≤

≤

k

×

8 closed knight’s tours have the property that moves k and
32? Hint: Deﬁne an exact cover problem.

×

a11 = 1, a16 = 16, a32 = 64, a52 = 32, a71 = 33, a83 = 34,

and such that 1
that moves 1, 2, . . . , 18 are rotated 180◦ from moves 49, 48, . . . , 32.)

18 implies a(9

j) = 50

aij

i)(9

≤

≤

−

−

−

aij . (The latter condition means

(cid:3) 301. [24 ] (G. E. Carpenter, 1881.) Find a knight’s tour for which the top row of the

step matrix is ‘1 4 9 16 25 36 49 64’.

(cid:3) 350. [M27 ] Exactly how many Hamiltonian cycles are possible in the Sierpi´nski gasket

(3)
n ? (See Fig. 113, near 7.2.2.3–(69).) Hint: There is a fairly simple formula.

graph S

(cid:3) 360. [25 ] An m

×

a Hamiltonian cycle of Pm Pn. For example, a few of the possibilities are

n meander frieze is a Hamiltonian cycle of Pm Cn that isn’t also

;

;

;

;

;

.

(i) 3 × 3

(ii) 3 × 4

(iii) 3 × 4

(iv) 4 × 4

(v) 5 × 4

(vi) 7 × 3

(Such friezes were often used as ornamentation on Greek vases of the “late Geometric”
period, c. 750 B.C. For example, the famous Dipylon Amphora was decorated in part
with the unusual frieze (vi) and several copies of (i) and (v).)

a) The margins of a meander frieze are the sequences v1 . . . vm

1 and h1 . . . hn, where
there are vi edges between rows i
1
and j. For example, the margins of (iv) are v1v2v3 = 242 and h1h2h3h4 = 1331.
True or false: vi is always even and hj is always odd.

1 and i and hj edges between columns j

−

−

−

b) Prove that no m
n meander frieze has m even and n odd.
c) A meander frieze is reduced if it doesn’t have vi = vi+1 = n or hj = hj+1 = m
for any i or j. (For example, (ii) reduces to (i) because it has h2 = h3 = 3.) Find
an example of an unreduced frieze for which v2 = v3 = n.

×

d) Draw all the meander friezes with m

≤

8 and n = 3. Are any of them symmetric?

December 4, 2025

(cid:12)
periodic
automorphisms
fourfold symmetry
torus
3D knight’s tours
knight graph
complement
central symmetry
fully symmetric
Grabarchuk graph
Euclidean distance
unit-distance graph, 3D
bipartite
regular
automorphisms
Hamiltonian decomposition
Wolf
chessboard

60

COMBINATORIAL SEARCHING (F8A: 4 Dec 2025 @ 1237)

7.2.2.4

e) An m

×

n meander frieze is periodic if it’s the same as d copies of an m
(n/d)
meander frieze, for some proper divisor of n. Draw all of the nonperiodic, reduced
meander friezes with m = 3 and n

8. Which of them are symmetric?

×

f) How many automorphisms does the graph Pm Cn have, when m, n
g) Count the nonisomorphic, nonperiodic, reduced meander friezes with 3
h) How many of the friezes in (g) are symmetrical?
i) Draw all of the friezes in (g) that have fourfold symmetry.

3?
m, n

7.

≤

≥
≤

≤

361. [M21 ] Describe the nonisomorphic Hamiltonian cycles of the torus C3 C4.

≤
0, 1
}
ijk

j < m, 0

369. [22 ] (3D knight’s tours.) The l
m
×
i(cid:2)j(cid:2)k(cid:2) where (i
k < n and edges ijk
0
≤
−
, say that the abc-complement of ijk is
If a, b, c
abc

×
−−−

∈ {

n knight graph has vertices ijk for 0

2

i(cid:2))

2

+ (j

j(cid:2))

−

+ (k

−

i < l,
2
≤
k(cid:2))
= 5.

and the abc-complement of edge ijk

= (a? l

1

i : i) (b? m

1

j : j) (c? n

−

−

−

−
i(cid:2)j(cid:2)k(cid:2) is (ijk

−−−

−−−

1
−
abc
i(cid:2)j(cid:2)k(cid:2))

k : k),
abc

−
= ijk

a) A cycle C in the l

m

n knight graph has central symmetry if (u

v

∈

×

−−−

×
C. Find a centrally symmetric 2

whenever u

b) Do centrally symmetric 4
c) Find a symmetry of the 4

3
×
4 knight’s cycles exist?
4 knight’s cycle (000 012 031 133 213 023 121 331
233 113 323 221 202 003 011 032 130 210 020 122 101 300 312 232 033 021 002
100 220 010 112 131 330 322 301 203 123 313 211 001 103 223 013 111 132 333
321 302 200 120 310 212 231 030 022 102 303 311 332 230 110 320 222 201).
d) Indeed, 48 of the 64 edges of that cycle form a set S that’s “fully symmetric,” in
the sense that every abc-complement of every edge in S is also present in S.

4 knight’s cycle.

×
×

×
×

4
4

×

∈

i(cid:2)j(cid:2)k(cid:2)
111
v)

abc

.
C

−−−
−−−

e) How many 4

4

4 knight’s cycles include all of the edges in that set S?
3

×

×

370. [M30 ] The Grabarchuk graph is the graph on 4
where xyz

x(cid:2)y(cid:2)z(cid:2)

the Euclidean distance between (x, y, z) and (x(cid:2), y(cid:2), z(cid:2)) is 3.

= 64 vertices xyz, 0

x, y, z < 4,

≤

−−−

⇐⇒

a) Prove that the Grabarchuk graph is bipartite, and regular of degree 6.
b) What are its symmetries (automorphisms)?
c) Find three Hamiltonian cycles that, together, contain all of its edges.

372. [20 ] (R. Wolf, 1894.) Choose a uniformly random square of the chessboard and
mark it ‘1’. After a square has been marked ‘k’, choose a uniformly random unmarked
square that’s a knight’s move away, and mark it ‘k+1’; but stop if there’s no such square.
Empirically estimate the probability that (a) the ﬁnal square is marked ‘k’,
i, j < 8;
64; (b) the ﬁnal square is in row i and column j, given 0

given 1
(c) the ﬁnal square is a knight’s move away from the starting square.
999. [M00 ] this is a temporary exercise (for dummies)

≤

≤

≤

k

December 4, 2025

[This is a page-ﬁller so that the answers will begin on a left-hand page.]

December 4, 2025

61

62

ANSWERS TO EXERCISES

7.2.2.4

After [this] way of Solving Questions, a man may steale a Nappe,
and fall to worke again afresh where he left oﬀ.

— JOHN AUBREY, An Idea of Education of Young Gentlemen (c. 1684)

SECTION 7.2.2.4

1. Established conventions promote communication, so they outweigh convenience.
[And we could save even more syllables by saying “HC” and “HP.” Many authors now
save two syllables by saying just “Hamilton cycles” and “Hamilton paths.”]

2. True (except in the trivial case where G has a single vertex). In fact, the number
of Hamiltonian paths in G is the number of Hamiltonian cycles in G(cid:2); the number of
= u in G is the number of Hamiltonian cycles in G(cid:2)
Hamiltonian paths between u and v
that include the edges by which u and v are joined to the new vertex.

AUBREY
Hamilton paths
Rote
inscribed cubes and tetrahedra
Br¨uckner
historical notes
Kowalewski
Du Val
threefold symmetries
stereographic projection
sphere

3. The 12 vertices of Fig. 121(a) are named ij for i

= j and 1

i, j

23, 12

12
where α is any even permutation of

24, and 12

43. If ij

−−−

−−−

−−−

i(cid:2)j(cid:2) then ji

≤
j(cid:2)i(cid:2) and (iα)(jα)
. These rules deﬁne all of the edges.

−−−

−−−

≤

−−−
1, 2, 3, 4

4. We deﬁne
(i(cid:2)α)(j(cid:2)α),

{

}

The 20 vertices of Fig. 121(b) are named ij for i

= j and 1

≤
j(cid:2)i(cid:2) and (iσ)(jσ)
12
where σ is the permutation (12345). These rules deﬁne all of the edges.

i(cid:2)j(cid:2) then ji

43, and 13

24. If ij

35, 12

−−−

−−−

−−−

−−−

−−−

≤

i, j

−−−

5. We deﬁne
(i(cid:2)σ)(j(cid:2)σ),

We can get from the dodecahedron graph of Fig. 121(b) to the icosahedron graph
of Fig. 121(a) by ﬁrst removing the eight vertices whose label includes ‘5’. Each of
the twelve vertices that remain can then be joined to its ﬁve nearest neighbors, which
were at distance
2 in the original graph. (This attractive labeling scheme for the
icosahedron was suggested by G. Rote in 2025.)

≤

Delightful patterns are abundant here! For example, if 1

5, exactly eight of
the dodecahedron’s vertices have a label containing l; and those eight vertices actually
are the corners of an inscribed cube. In fact, the four vertices with left coordinate i are
equidistant, and they’re the corners of the ith “inscribed left tetrahedron”; similarly,
the four with right endpoint j deﬁne the jth inscribed right tetrahedron. Thus vertex
ij is the intersection of two inscribed tetrahedra.

≤

≤

l

[See M. Br¨uckner, Vielecke und Vielﬂ¨ache: Theorie und Geschichte (Leipzig, 1900),
105; A. Kowalewski, Sitz. Akad. Wiss. Wien (IIa), 126 (1917), 67–90, 963–1007;
§
P. Du Val, Homographies Quaternions and Rotations (Oxford, 1964),
2.11. See also
exercise 7.2.2.1–136 for a 3D-geometry-based representation scheme.]

§

to

14+53
2

31+54
2

; (ii) from

4. It remains unchanged after 180◦ rotation about any of the following lines: (i) from
13+45
2

; (iii) from
There also are remarkable threefold symmetries of a diﬀerent kind: Color the edges
of the cycle alternately red and green; color the other edges blue. Then a 120◦ rotation
about any of the lines from 21 to 12, 23 to 32, 24 to 42, or 25 to 52 will permute the
colors cyclically(!). That will yield green-blue and blue-red cycles (see exercise 24).

15+34
2

51+43
2

41+35
2

to

to

.

{

12

−−−

5. We can redraw the edges

35, 51
}
so that they lie outside the circle. Alternatively, via stereographic projection we can
regard a planar graph as a graph embeddable on the surface of a sphere. In this sense
Figure 122(c) shows the Hamiltonian cycle on the equator; we can imagine that half of
the other edges lie in the hemisphere below. [A cubic planar graph with a Hamiltonian
cycle can always be drawn as a circle, with some of the unused n/2 noncrossing edges
inside and the others entirely outside. See exercise 103 for more about planarity.]

34, 53

24, 45

13, 21

−−−

−−−

−−−

−−−

42

December 4, 2025

(cid:12)
(cid:12)
(cid:12)
7.2.2.4

6, 7, 8.

ANSWERS TO EXERCISES

63

13

24

32

41

14

21

43

12

31

42

23

34

a

e

b

f

9

d

8

0

c

4

1

5

3

7

2

6

32

51

24

25

43

35

31

12

45

14

21

13

53

41

52

42

54

34

15

23

complex plane
golden ratio φ
Gerbracht
multigraph
parity

iθ

To determine the distances and angles needed for the third drawing above, assuming
, solve
that vertex ‘12’ is point 1 in the complex plane and that ‘35’ is point re
i(θ
re
1
. The answer (see exercise 1.2.8–19) is
|
−
r = 5−
.5536. [E. H.-A. Gerbracht, Kolloquium
−
¨uber Kombinatorik, Universit¨at Magdeburg (15 November 2008).]

e
|
|
.5257, θ =

−
1
2 arctan

=
φ−

|
≈

1
|
1/2

re
π
4

−
≈

2π/5)

|
1/4

iπ/5

re

=

1
2

iθ

iθ

−

2

2

2

43

32

14

25

−−−

−−−

−−−

9. (a) We can assume by symmetry that the cycle begins at vertex 12, having just
come from 35. Case (i) takes us to 54, 23, 41, 35; oops! In case (ii) it’s 54, 31, 25, 14;
now 43 is stranded. In case (iii) the moves to 54, 31, 42, 53, 21, 45, 13 force the cyclic
path 51
51. The opening moves 54, 23, 15, 34 in cases
(iv)–(vi) force the ending to be . . . , 51, 24, 13, 52, 41, 35; so those cases are ruled out.
2
.
10. All but 23, 24, 25, 31, 41, and 51. (There are 20 Hamiltonian paths from 12 to 35,
in spite of the “uniqueness” of exercise 9. There are only six such paths from 12 to 21.)
11. Let aj = (2j)(cid:2), bj = 2j, cj = 2j + 1, and dj = (2j + 1)(cid:2). Notice that GP(2q, 2) is a
3, a multigraph for q < 3. The ungeneralized Petersen graph is GP(5, 2).
graph for q
A Hamiltonian path P can be characterized by its endpoints and its 3-bit “states”

(b) The only remaining possibilities are (LLLRRRLRLR)

and (RRRLLLRLRL)

−−−

−−−

≥

2

sj = [aj

(cid:0)

aj

P ][cj

(cid:0)

bj

P ][dj

(cid:0)

dj

P ],

0

j < q,

j(cid:2) = (j + 1) mod q.

{

∈

∈

≤

a2

−−−

∈
a0, a1

d2
a1. Moreover, the states (s0, s1, . . . , sq

−−−
and q = 3, the states (s0, s1, s2) = (011, 111, 010)
}
d0
b0
−−−

−−−
For example, with endpoints
can arise only from the path a0
−−−
−−−
−−−
b2
1) = (011, 111, . . . , 111, 010)
yield a path from a0 to a1 whenever q
a0 then gives a
Hamiltonian cycle.) Those same states also deﬁne a Hamiltonian path from a0 to c1.
(cid:0)
are possible. For example, parity is pre-
sj
contains no endpoint; and the only such legal transitions are

d1
2, sq
3. (Adding the edge a1

Only certain state transitions sj
, dj

served if

−−−
−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

, bj

, cj

→

aj

c1

b1

c0

c2

≥

−

(cid:0)

(cid:0)

(cid:0)

(cid:0)

001

{
100, 001

}
111, 010

→

000

→
101, 011

→
110, 101

111, 100

001, 111

010, 111

100, 111

111;

→
000, 101

→
011, 110

→
011, 110

→

101.

→

→

→

→

→

→

Certain additional restrictions also apply. For example, 110
once, or it will “disconnect” the path. The sequence 001
Parity is preserved also when both endpoints lie in

→
(cid:0)
aj

011 can be used at most
010 forces a 5-cycle.
. For example,
, dj

→
, cj

(cid:0)

(cid:0)

→
111
(cid:0)
, bj

we get a path from a0 to d0 for all q

2 from the sequence (111, . . . , 111, 010).

Transition rules at parity changes are also easy to work out. For example, if aj

(cid:0)

is

≥

{

}

an endpoint the legal transitions are

000

001, 011

010, 011

100, 011

111, 110

001;

→
000, 001

→
011, 010

→
011, 010

→
101, 111

→
000, 111

→

→

→

→

011.

→

001

→

It turns out that Hamiltonian paths from a0 to v exist except when v lies in Bq,
j mod 3 = 2,

aj

where Bq =
0 < j < q

j mod 3 = 0, 0 < j < q
}
{
when q mod 3 = 1; and Bq =
{

|

}

|

when q mod 3 = 0; Bq =
aj

aj
= 1, 0 < j < q

j mod 3

{

bj

j mod 3 = 1, 0 < j < q

when q mod 3 = 2. (Unless q < 4: B3 =

1

−

} ∪

|
} ∪ {
b1, b2
{

c0, cq
.)

}

|

{
December 4, 2025

}

(cid:12)
generating functions
Lucas number
Fibonacci numbers
planar
triconnected
Garey
Johnson
Tarjan
isomorphic
Petersen graph
Giridhar
Hamiltonian path

64

ANSWERS TO EXERCISES

7.2.2.4

12. Consider the state transitions in answer 11. The legal cycles of odd-parity states
k
are of two kinds, namely (010, 111∗, 111)
; here ‘111∗’ stands
for zero or more repetitions of 111. Two legal cycles of even-parity states exist when
q = 3k + 2, namely (000, 101, (011, 110, 101)

) and (110, (011, 110, 101)

and (001, 111∗, 100)

, 011).

k

k

k

2 + 2q[q mod 3 = 2], where Lq = Fq+1 + Fq

The number of Hamiltonian cycles is the number of legal cycles of states, and
we can enumerate them by using generating functions. The answer turns out to be
2Lq
14. (a) In fact, let H be any induced subgraph whose vertices all have degree 3 except
for exactly two vertices of degree 2. The other edges from those two must be true in
every win, or we’d have a cycle entirely within H.

1 is the qth Lucas number.

−

−

(b) The connecting edges are 1, and so are many of the internal edges. Thus
internal cycles will appear when x + y + z is 0, 2, or 3. (But if x + y + z = 1 we easily
have a path through all the internal vertices.)

(c) The long horizontal edges must be true, because consecutive true vertical edges
would yield a short cycle. Hence the edge values at the left and right are x, ¯x, x, ¯x, x
and y, ¯y, y, ¯y, y. If x = y we’d have a 4-cycle or two 8-cycles.

(d) Hook Cm to C1. Then insert XOR gadgets to ensure that all appearances of
[This construction can be extended so that
the same variable have consistent values.
G is not only cubic but planar, and triconnected, with at least ﬁve sides on every face.
See M. R. Garey, D. S. Johnson, and R. E. Tarjan, SICOMP 5 (1976), 704–714.]

16. (1, 2, 5, 19) connected cubic graphs on (4, 6, 8, 10) vertices are essentially distinct
(not isomorphic); we’ll study how to generate them in Section 7.2.3. They all are
Hamiltonian except for two of order 10. One of the latter is the famous Petersen graph
(Fig. 2(e) near the beginning of Chapter 7), which also is nonplanar.

The other “smallest” non-Hamiltonian example is actually planar:
[Arun Giridhar veriﬁed in 2015 that a 16-vertex variant of this graph,
consisting of three 5-vertex diamonds joined to a central vertex, is (uniquely) the
smallest cubic graph that has no Hamiltonian path.]

.

18. False. For example, consider 0
−−−
20. (a) The condition holds when ak is the number of k-sided faces inside the n-cycle.
For it’s certainly true when there’s just one such face (ak = [k = n]). And if a new
chord is added to the graph, breaking an inner p-face into a q-face and an r-face where
q + r = p + 2,

2)ak changes by (q

0, 0

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

k(k

2)

0.

1

2

3

4

5

2

4

[The number a(cid:2)k = αk
(cid:14)

−

Kirkman’s conditions. Indeed, we always have
edges

vertices

faces

=

(cid:19)

(cid:20) − (cid:19)

(cid:20)

(cid:19)

−

(cid:20) −

−

2) + (r

(p
ak of k-faces outside the cycle is also a solution to
k αk =

1
2)αk =
2
2 in a connected planar graph.]

2) = 0.

k kαk

k(k

(cid:14)

(cid:14)

(cid:14)

−

−

−

−

−

1
2

(b) We can assume that the missing vertex is outside the cycle; and 3a5 can’t

equal 19

2. (The dodecahedron does have cycles of lengths

5, 8, 9, 10, . . . , 17, 18

.)

(c) We can assume that neither cycle is inside the other. A cycle that contains

{

}

−

exactly a pentagons has length 3a + 2; and (3a + 2) + (3b + 2) can’t equal 20.

−−−

(d) Let G(cid:2) be G without the edge a

b, and with two additional vertices of
degree 2: one inserted between a and f , another between b and c. Any Hamiltonian
b corresponds to a Hamiltonian cycle in G(cid:2). But G(cid:2) isn’t
cycle in G that omits a
Hamiltonian, because α(cid:2)k = [k = 4] + 7[k = 5] + [k = 11] and 2a(cid:2)4 + 3a(cid:2)5 + 9a(cid:2)11
2.
(e) Graph (i) has αk = [k = 4] + 20[k = 5] + 2[k = 11]; graph (ii) has αk =
[k = 4] + 18[k = 5] + 4[k = 8]. So both of them fail Kirkman’s test (a). Graph (iii), with
αk = 18[k = 5] + 3[k = 6] + 3[k = 8], passes the test only if a6 = 0 or 3. But the three
6-edged faces can’t all be inside or outside the cycle, since they share a common point.

= 18

−−−

−

December 4, 2025

(cid:12)
Historical notes
Hamilton
Grinberg
Faulkner
Younger
cyclically 5-connected
automorphisms
gadget
Kirkman
Faulkner
Younger
Grinberg
3-cube
Grinberg
Historical notes
r-regular graph
“Star of David” graph

7.2.2.4

ANSWERS TO EXERCISES

65

[Historical notes: As noted near the beginning of this chapter, Kirkman actually
studied full-length cycles in convex polyhedra before Hamilton began to toy with
[See Philosophical Transactions 146 (1856), 413–418.] Graphs (ii) and
such ideas.
(iii) in part (e) are due to ´E. Ya. Grinberg, Latvi˘ıski˘ı Matematicheski˘ı Ezhegodnik
4 (1968), 51–58, who rediscovered Kirkman’s long-forgotten criterion. Graph (i) was
found as part of an exhaustive computer search by G. B. Faulkner and D. H. Younger,
Discrete Math. 7 (1974), 67–74, who also established that Grinberg’s (iii) is the unique
smallest cubic planar graph that is cyclically 5-connected : It cannot be broken into
two components each containing a cycle unless at least ﬁve edges are removed. (Graph
(ii) clearly has four automorphisms; and graph (iii), obtained by adding a single edge,
actually has six, although that isn’t obvious from the diagram. If we add another edge
at the right, in the mirror-image position, we get a 46-vertex graph with 36 Hamiltonian
cycles. Of course each of those cycles uses both of the edges that were added to (ii).)]
21. Among many possibilities, the simplest are perhaps the (20n + 2)-vertex graphs

FYn =

B

B

· · ·

B

B , where graph (i) in exercise 20(e) is
made from n copies of an 18-vertex gadget
FY2 and B
In general, FYn has αk = [k = 4] + 10n[k = 5] +
2[k = 5n + 1]; so it fails Kirkman’s test whenever n mod 3 = 2. Further analysis, based
on the fact that each of the four graphs

is illustrated there.

B

B

,

B

B

,

B

B

,

B

B

also fails Kirkman’s test, shows that FYn is actually non-Hamiltonian for all n > 1.

(Faulkner and Younger went on to show that the 78m-vertex graphs

B

B

· · ·

B

, where

B =

B

B

B

B

,

s

s

·

·

3

⊕

−

−

10

)(3t

−−−
−−−

5, 3
7, 4

7: 12 auts, 6H, perfect (two sets of three). Case 3, 0

are not only non-Hamiltonian, they can’t be covered by fewer than m disjoint cycles.)
Grinberg’s paper of 1968 described non-Hamiltonian cubic planar graphs having
4
(14
1) vertices, for any s, t > 0. His graphs are noticeably harder
than FYn for a computer to analyze; even the case (s, t) = (2, 1) is quite a challenge.
24. (a) K4
K4 is disconnected (and K4 is perfectly Hamiltonian). The others are
at least Hamiltonian, and we can number the vertices so that 0
0.
−−−
7: 16
There are ﬁve nonisomorphic possibilities: Case 1, 0
−−−
2,
auts, 4H. [Translation: 16 automorphisms and 4 Hamiltonian cycles.] Case 2, 0
−−−
5,
2, 1
1
−−−
7: 48
3
auts, 6H, planar [the 3-cube]. Case 5, 0

6, 4
6: 4 auts, 3H, planar, perfect. Case 4, 0

4, 1
(b) Let ak be the number of k-faces inside none of the three Hamiltonian cycles; let
bk, ck, dk be the number that are inside cycles
, respectively. Then
Kirkman’s criterion for cycle 1 is satisﬁed by bk + ck and ak + dk, the number of faces
respectively inside or outside. Similarly, it’s satisﬁed for cycle 2 by bk + dk and ak + ck;
2)dk; we’ve
for cycle 3 by ck + dk and ak + bk. Let A =
−
2. [See Grinberg’s paper in answer 20.]
shown that A+B = A+C = A+D = B+C = n
(cid:14)
(cid:14)
[Similarly, an r-regular graph is perfectly Hamiltonian if its edges can be r-colored
(The 4-regular
in such a way that all
6-vertex “Star of David” graph L(K4) is a good example; so is the 5-regular K6.) Such

−−−
5, 4
−−−
7: 16 auts, 5H.

pairs of colors yield Hamiltonian cycles.

−−− · · · −−−
6, 5
−−−

2)ak, . . . , D =

1
−−−
3, 4

−−−
−−−

2, 1

3, 1

6, 2

5, 2

6, 3

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

1, 2

1, 3

2, 3

k(k

k(k

−

−

r
2

7

{

}

{

}

{

}

,

,

(cid:15)

(cid:16)

December 4, 2025

P1F
1-factors
perfect matchings
Kotzig
Fiedler
Labelle
strongly H graphs, see perfectly H graphs
Rosa
Halin graphs
Historical notes
isthmus
bridge
cyclically 2-connected
bridge, wheatstone
Tait
cyclically 3-connected
Four Color Theorem
Tutte
Barnette
Bos´ak
Lederberg
Holton
McKay
Kardoˇs
fullerene graphs
author
3D-printed
all Hamiltonian paths
rank
Tait

66

ANSWERS TO EXERCISES

7.2.2.4

neighbors have respectively

graphs are also called P1F, “perfectly 1-factorable,” because two 1-factors — also known
as perfect matchings — are called perfect if they yield a Hamiltonian cycle, and because
an r-regular graph with χ(L(G)) = r is called 1-factorable. The pioneering explorations
of A. Kotzig (see Theory of Graphs and its Applications, ed. by M. Fiedler (1964), 63–
82) have led to a large literature with many provocative problems still unsolved (see
A. Kotzig and J. Labelle, Annales des Sciences Math. du Qu´ebec 3 (1979), 95–106); for
an excellent survey see A. Rosa, Mathematica Slovaca 69 (2019), 479–496. Answer 124
below, Case 2, proves incidentally that cubic Halin graphs are perfectly Hamiltonian.]
27. (a) This follows directly from exercise 20(d). (In general, we get a “forcing” gadget
from any graph that has a “forced” edge, by removing any vertex of that edge.)
(b) Insert a degree-2 vertex into each of those spokes and apply 20(a).
(c) Two nonconsecutive spokes are forced to be in any Hamiltonian path.
(d) No. One of the ﬁve 4-faced regions touches the unique 9-faced region. Its other
faces.
,

5, 7, 7
Historical notes: A cubic graph that can be disconnected by removing
one edge is clearly non-Hamiltonian. Many cyclically 2-connected planar cubic
graphs, such as the example shown, also have no Hamiltonian cycle. However,
P. G. Tait investigated numerous cyclically 3-connected planar cubic graphs —
the “true” polyhedra — and found Hamiltonian cycles easily. So he conjectured that
such cycles always exist, and he pointed out that the famous “Four Color Theorem”
would then follow. (See
16 of his paper cited in answer 35.) Tait’s conjecture
was believed for many years, until W. T. Tutte [J. London Math. Soc. (2) 21 (1946), 98–
101] found a 46-vertex counterexample by putting together three Tutte gadgets. The
smaller graphs in (c) were found independently in 1964 by D. Barnette, J. Bos´ak, and
J. Lederberg; those graphs are the only counterexamples with fewer than 40 vertices
[see D. A. Holton and B. D. McKay, J. Combinatorial Theory B45 (1988), 305–319].
Every counterexample has a face with more than 6 vertices [F. Kardoˇs, SIAM J. Discrete
Math. 34 (2020), 62–100]; in particular, all “fullerene graphs” are Hamiltonian.
30. We can use the Ls and Rs of answer 8 as a guide:

15 and

7, 7, 7

5, 8, 8

7, 7, 8

5, 7, 8

7, 8, 8

{

}

{

{

}

}

}

{

{

}

{

}

§

§

,

,

,

,

A

E

D
BC
F
G
RS

Q

E
F
T
S
T
S
R

A

B

AT

ML

B

C

C

D

KJ

L

IH

J

D

FE
G
H

NM LM
N

K JK

I HI

G R

ON

Q P

O

P

O

Q

P

(The author cherishes a 3D-printed object like this, received as a surprise gift in 2016.)
33. nH + h — one for every Hamiltonian path in G (cyclic or not). (Thus an algorithm
that ﬁnds all Hamiltonian cycles can readily be adapted to ﬁnd all Hamiltonian paths.)
35. (a) The tour lines divide the plane into regions. Every such region can be assigned
a rank, representing its distance from the outside. (More precisely, the rank is the
minimum number of tour lines crossed by any path in the plane that goes from a point
in the region to a point outside the chessboard, without passing through any of the
tour’s intersection points.) Then, as you walk along the tour, make your thread go on
top at an intersection if and only if the region on your left has odd rank. [See P. G. Tait,
London, Edinburgh, and Dublin Philosophical Magazine 17 (1884), 30–46,

19.]

§

December 4, 2025

7.2.2.4

ANSWERS TO EXERCISES

67

(b) One endpoint is in the outside region, but the other is in a region of rank 4.
Any artiﬁcial path that connects the two, and crosses k tour lines, will lead to a drawing
with k exceptions when the artiﬁcial path is removed. Conversely, the exceptional tour
segments in any drawing can be crossed by an artiﬁcial connection path together with
zero or more artiﬁcial cycles; so there must be at least 4 exceptions.

(There’s no problem in (2), because each endpoint lies in the outer region.)

open
Rudrat.a
poetic license
Murray
silver general
sh¯ogi
Japanese chess

36. In (i), σ22

σ24 and σ25

↔

↔

σ27. In (ii), ‘lots’ matches ‘lost’:

(cid:9)B(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:18)p

(cid:9)q(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:18)p

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)(cid:139)(cid:4)

(cid:9)(cid:18)(cid:5)

(cid:9)|(cid:5)

(cid:9)J(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:10)p

(cid:9)J(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)(cid:10)"

(cid:8)-"

(cid:3)1"

(cid:9)u#

(cid:3)1"

(cid:3)!"

(cid:9)w(cid:26)

(cid:3)<(cid:8)

(cid:9)Dp

(cid:7)(cid:128)"

(cid:9)s>

(cid:3)w(cid:5)

(cid:3)(cid:128)"

(cid:9)-"

(cid:3)u(cid:26)

(cid:3)<(cid:8)

(i)

(cid:9)EF

(cid:8)d(cid:11)

(cid:9);>

(cid:9)g=

(cid:8)a>

(cid:9)g=

(cid:8)i[

(cid:3)j(cid:8)

;

(ii)

(cid:9)k>

(cid:7)]=

(cid:8)i=

(cid:9)z>

(cid:3)f=

(cid:8)E=

(cid:9)z[

(cid:3)(cid:130)(cid:8)

.

(cid:9)k"

(cid:9)m"

(cid:9)y#

(cid:9)n"

(cid:9)m#

(cid:9)nR

(cid:9)z.

(cid:9)o(cid:8)

(cid:9)k=

(cid:9)a"

(cid:9)(cid:140)=

(cid:9){=

(cid:9)a"

(cid:9)ǱR

(cid:9)c.

(cid:9)b(cid:8)

·

37. Starting at cells (1, 2, 3, 4) of row 1 we obtain respectively (7630, 2740, 2066,
3108) tours. Starting at cells (1, 2, 3, 4) of row 2 we obtain none. Thus there are
exactly 4
(7630 + 2740 + 2066 + 3108) = 62,176 tours, all of which are open because
they begin and end in the top or bottom row. (Among all such tours, 1904 cannot
be represented by a single Rudrat.a-style sloka because all 32 syllables of such a sloka
would have to be identical! Only the example in answer 36(ii), and its reversal after
180◦ rotation, are representable by a sloka that has 12 distinct syllables.)
38. One knight jumps like three rookwise steps.

Past sore too mean; so, just for free,
Hops here, turns there, ﬂies each goose now.
Can’t place last word? Won’t ﬁnd the sea.
One, two, three, four! See each word here:
Jumps so wise now ﬁnd their place passed.
Terns can’t soar, like ﬂies the free rook;
Goose steps just won’t mean knight hops last.

40. Meet me, you fool; trip some word up;

Eat, see if autumn is a mess.
To forgo this ordeal, I cheat:
Won three games like dice, card-trick, chess.
One, two, three, four! Games go like this:
Dice or card deal, tricky chess cheat,
Mess up; a word is some dumb trip.
Awful if you see me eat meat.

[Sloka 16 in Rudrat.a’s K¯avy¯ala ˙nk¯ara can be interpreted as two poorly joined quarter-
tours of an elephant. See Murray’s History of Chess, pages 54 and 55.]

(A “silver general” in sh¯ogi (Japanese chess) has the same moves as an elephant.)

±

−

±

1, j

1, j), plus 4(m

41. (a) There are (m
“leg” arcs from (i, j) to (i

1)n “trunk” arcs from (i, j) to (i
1); total (m
(b) Yes: If and only if m = 2 and n is even. (Use just two trunk moves.)
(c) In fact, the solution in Fig. A–18(a) is the only such Hamiltonian path on E48.
)
(d) If not, every vertex of row 1 is of type A (
within the path. There’s a B at the left and an A at the right. The adjacent pairs
AD, BD, CA, CB are not permitted, nor are the near-adjacent pairs B
D,
C (with one vertex intervening). Furthermore the substrings B(CD)∗A =
D
are forbidden, because these are closed cycles and m > 2.

◦
BA, BCDA, BCDCDA, . . .

) or D (

) or C (

) or B (

1)(5n

A, D

A, B

C, C

1)(n

−
4).

1)

−

−

−

−

◦

◦

◦

◦

{
December 4, 2025

}

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
2
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:12)
%
3
(cid:13)
(cid:14)
)

(cid:16)
9
(cid:24)
:
#
7
&
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:5)
.
&
(cid:6)
/
K
0
(cid:2)
(cid:7)
(cid:3)
(cid:29)
$
.
3
N
8

*
P
(cid:7)
#
(cid:5)
%
&
(cid:6)
(
)
+
:
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
.
&
(cid:30)
/
K

0
(cid:2)
(cid:7)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
)
(cid:15)
W
9
X
Y
(cid:0)
(cid:19)
(cid:20)
.
x
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:4)
(cid:20)
O
(cid:31)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
@
N
(cid:14)
(cid:15)
e
(cid:17)
P
(cid:0)
(cid:4)
(cid:11)
(cid:20)
O
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
M
3
N
x
(cid:31)
h
e
(cid:17)
P
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
&
(cid:6)
(cid:129)
(
(cid:15)
*
\
5
Y
>
(cid:29)
(cid:26)
(cid:20)
3
(cid:13)
O
V

(cid:8)
(cid:3)
(cid:29)
(cid:5)
$
7
(cid:30)
N
8
(cid:31)

*
9
Y
(cid:7)
(cid:26)
$
%
(cid:6)
’
*
9
,
(cid:7)
(cid:8)
}
(cid:29)
(cid:26)
3
(cid:13)
K

(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
$
7
&
(cid:30)
N
t
K

*
+
Y
(cid:7)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
(cid:11)
$
%
‘
3
N
(
(cid:31)
h
*
+
5
,
(cid:19)
M
%
N
x
e
9
(cid:24)
Y
(cid:0)
>
(cid:29)
@
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
$
%
@
3
N
(cid:31)

*
9
,
(cid:7)
(cid:8)
(cid:4)
(cid:19)
$
%
N
(cid:14)
W
9
(cid:24)
Y
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
@
3
(cid:14)
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
68

ANSWERS TO EXERCISES

7.2.2.4

But no string of A’s, B’s, C’s, and D’s obeys all of those restrictions.
(e) The same proof works, with types A (
(f) The vertices of (d) are joined by one of type E (
). The leftmost
is either B or F; the rightmost is either A or E. Cases B
C are
excluded, in addition to those of (d). Exactly n [n even] such sequences are possible,
having the forms F(CD)∗A, B(CD)∗ED(CD)∗A, B(CD)∗CF(CD)∗A, or B(CD)∗E.

) or F (
E, D

), and D (

), C (

), B (

A, F

E, F

).

◦

◦

◦

◦

Each of these has exactly one unsaturated vertex in row 2. Thus there are one or

directed graphs
ZDD
oriented cycles
generating function

two possible moves to row 3, and we’ve eﬀectively reduced m to m

2.

−
) or F (

(g) Now the vertices of (e) are joined by one of type E (

) or G ( ). The
leftmost is either B, F, or G; the rightmost is A, E, or G. The new forbidden substrings
are AE, BE, CG, FA, FB, GD, C
D. Six species of solutions exist, namely
◦
GA∗(CD)∗A, B(CD)∗B∗G, B∗FD(CD)∗A, BCD(CD)∗B∗FD(CD)∗A, B(CD)∗CEA∗, and
B(CD)∗CEA∗(CD)∗CDA. The solutions containing A∗ or B∗ work when n is odd.
2 and continue. (By induction, m must be even.)

E, F

be the n

is the number of Hamiltonian paths
(m)
from (1, i) to (m, j); let B
counts paths from (m, i) to (1, j).
ij
(These matrices are symmetric about both diagonals, because the left-right and top-
bottom reﬂections of any elephant path are elephant paths, possibly reversed.) We have

×
(m)

−
n matrix where a
be analogous, where b

(m)
ij

Again we reduce m to m
(h) Let A

(m)

◦

(2)
ij = ([i = j = 1] + [i = j = n] + [
(2)
ij =

a

b

[i odd][j even][i < j ] + [j odd][i even][j < i],
[i odd][j odd] max([i = 1], [i = n], [i

= j ]),

(cid:17)

i

|

j

|

−

if n is even,
if n is odd,

= 1 and max(i, j) odd])[n even],

by (f) and (g). Moreover, by considering moves between two-row subgraphs,
(cid:0)

(cid:0)

(cid:0)

(cid:0)

(m+m

)

(m)

(m

)

(m+m

)

(m)

(m

)

A

= A

XA

= B

(X +I)B

, where xij = [

i

j

= 1].

and B
(4)

A

+

(cid:14)

(cid:14)

(4)

B

= 14 + 120 = 134 tours on a 4

×

|

−
|
8 board.

For example, there are

s

(a)

t

(b)

(c)

Fig. A–18. Noteworthy paths and cycles for elephants.

×

42. The technology of exercise 7.1.4–226 can be extended to directed graphs in a
straightforward way. It constructs a ZDD of about 1.3 meganodes for all oriented cycles
8 elephant digraph, and shows that there are exactly 277,906,978,347,470 of
in the 8
them. The generating function by cycle length is 98z
+
50128559z
. If we say that trunk moves have weight 2 while other moves
have weight 3, we ﬁnd (by computing maximum-weight cycles) that exactly four of the
6544 62-cycles have only eight trunk moves. All four of these solutions are equivalent
under reﬂection to Fig. A–18(b).

+ 6544z

+ 3853z

+ 205z

+ 698z

· · ·

+

60

62

2

4

6

8

(Figure A–18(c) shows an interesting symmetrical 60-cycle that omits the corners

and has just four trunk moves.)

December 4, 2025

(cid:12)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:8)
(cid:9)
7.2.2.4

ANSWERS TO EXERCISES

69

44. We can use Rudrat.a’s half-tour twice:

Bah dee boo dai hao fuh hoe fay, bee doo bai fao huh foe hay dah?

Fee hah day boe foo hai dao buh, fai bao duh hoo doe bay fah hee.

Lah mee loo mai sao nuh soe nay, lee moo lai nao suh noe say mah?

Nee sah may loe noo sai mao luh, nai lao muh soo moe lay nah see!

(This is an open tour. See exercise 199 for closed tours that rhyme just as perfectly.)

Rudrat.a
open tour
closed tours
Ibn Man¯ı‘
Murthy
Rudrat.a
Ratn¯akara
De´sika
de Jaenisch
von Warnsdorf

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:11)

(cid:9)s(cid:11)

(cid:9)s(cid:4)

(cid:9)gr

(cid:9)J(cid:26)

(cid:9)s(cid:8)

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:3)np

(cid:7)u#

(cid:9)(cid:137)"

(cid:7)JM

(cid:3)Q(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)d=

(cid:9)k>

(cid:9)I=

(cid:8)_=

(cid:3)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)(cid:10)"

(cid:9)(cid:128)>

(cid:9)QF

(cid:3)z>

(cid:9)u(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)Z"

(cid:0)(cid:22)(cid:11)

(cid:0);(cid:20)

(cid:9)j=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G#

(cid:3)Ǳ=

(cid:9)k"

(cid:9)m"

(cid:9)o.

(cid:9)y=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)=

(cid:9)(cid:131)M

(cid:3)(cid:130)(cid:8)

(cid:9)(cid:127)"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1F

(cid:9){.

(cid:9)b(cid:8)

46. This tour is rather like that of Ibn Man¯ı‘ in (1):

[G. S. S. Murthy, in Resonance 25 (2020), 1095–1116, comments further on the
work of Someshvara, and gives excellent translations of the Sanskrit verses by Rudrat.a,
Ratn¯akara, and Ved¯anta De´sika.]

×

50. In fact, the text’s “merry chase” need not end at cell 22; by swapping 23
25
we get a tour that ends at 02. The other seven choices of 9 and 10 can lead, similarly,
to either 22 or one of

. Each case completes an open tour.

02, 11, 13, 20, 24, 31, 33

↔

[See page 280 of de Jaenisch’s book, for his analysis of 5

5 paths.]

{

}

51. Again v1v2v3v4 = 00 12 04 23 without loss of generality. Now t1 = 44 forces
v5 = 31, and there’s a tie for v6. If v6 = 43, the path continues v7 . . . v15 = 24 03 11 30
42 34 13 01 20; and v16 is 32 or 41. The former case forces v17 = 40, hence “shutting
out” 44; it leads to four paths, each ending at v24. But the latter case leads to three
paths, two of which end with v25 = 44 (yea) and one that ends with v21 = 44 (boo).

On the other hand if v6 = 10 we get v7 . . . v13 = 02 14 33 41 20 01 13 and then
v14v15v16 = 21 40 32 or 32 40 21. Either case shuts 44 out. Ten continuations are
possible, each of which involves 24 vertices — all but cell 44 (close but no cigar).

(The randomized algorithm of exercise 53 will yield a Hamiltonian path with
3
8 .)

and r = 3, this probability rises to

3
16 . If we set

23, 32, 44

t1, t2, t3

=

probability

{

}

{

}

52. The algorithm acts just as if a double-target vertex t has been entirely removed
from the graph, because DEG(t) will never be less than 2n in step W5.

53. W5(cid:2). [Is DEG(u) smallest?] If t < θ, set θ
set q

q + 1, then set v

u with probability 1/q.

←

t, v

←

←

u, q

←

←

1. Otherwise, if t = θ,

55. Ibn Man¯ı‘ broke Warnsdorf’s rule ﬁrst when choosing v14 = 41 instead of 06. His
choices for v26, v27, v38, v39, v45, v48, and v54 also broke the rule. But altogether, his
“hug the edge” strategy followed it
87% of the time, so he probably had some of
the same intuition that von Warnsdorf acquired later. Similarly, Someshvara deviated
only eight times. But al-‘Adl¯ı broke the rule 15 times, clearly thinking other thoughts.

55
63

≈

56. If there’s no remaining exit from u, there’s no remaining entrance to u. Therefore
Algorithm W will not ﬁnd a Hamiltonian path unless it moves to u. We might as well
do that, if our goal is simply to ﬁnd a Hamiltonian path. But maybe we really want
to ﬁnd as long a path as possible, via Warnsdorf-like rules; then we can do better.

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
(cid:29)
.
&
3
t
)

0
(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
7
&
3
t
)

+
:
(cid:2)
(cid:7)
T
&
(cid:6)
/
(cid:15)
\
5
:
(cid:2)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
p
(cid:26)
%
&
(cid:30)
(cid:13)
(
V
4
\
5
:
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:19)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:5)
&
(cid:6)
(
(cid:31)
0
(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
(cid:19)
$
3
N
(cid:14)

e
(cid:24)
P
>
(cid:5)
%
&
(cid:6)
(
(cid:31)
\
:
(cid:2)
(cid:7)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:23)
(cid:6)
(cid:13)
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
.
O
8
(cid:31)
(cid:0)
(cid:2)
(cid:3)
$
@
N
)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
U
(cid:11)
3
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
>
(cid:4)
(cid:11)
(cid:19)
M
%
&
N
x
(
V
(cid:15)
e
\
(cid:17)
Y
(cid:19)
[
.
N
(cid:21)
8
(cid:15)
W
X
P
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
N
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
@
N
(cid:14)
(cid:15)
e
X
P
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
backtrack algorithm
convex triangular grid graphs
SGB
simplex
dual
triangular faces
convex polygon
Gray binary code
delta sequence
ruler function ρ

70

ANSWERS TO EXERCISES

7.2.2.4

Vertex u is a dead end if and only if DEG(u) is 0 or n. Suppose vk has just two
neighbors, u and u(cid:2), where DEG(u) = 0 and DEG(u(cid:2)) = n. We presumably should choose
vk+1 = u(cid:2) in such a case, because u(cid:2) is one of the designated targets.

Thus we can improve the algorithm by changing ‘t < θ’ in step W5 to ‘f (t) < f (θ)’,

where f (0) = 2n + 1, f (n) = 2n, f (t) = t + 2 for t

2n, and f (t) = t otherwise.

57. This is a simple backtrack algorithm, following the outline of Algorithm 7.2.2B.
Leaves of the search tree correspond to the paths of Algorithm W. The probability of
each node is the probability of its parent, divided by the family size.

≥

9

59. Build 64 anti-Warnsdorf trees, as in exercise 57. There are 8 paths v1v2 . . . v20
of length 19 (equivalent to each other via rotation/reﬂection), each occurring with
probability 2−
.0000027; they actually turn out to be cycles of length 20. At
the other extreme, there are 24 anti-Warnsdorf paths as long as 53, of which 8 have
probability p = 2−
.0000000039 and 16 have probability 3p; representatives are
shown below. The mean path length is

34.8, and the standard deviation is

5.3.

3−

3−

≈

≈

20

5

6

≈

≈

By contrast, Algorithm W will ﬁnd a path that’s longer than every anti-Warnsdorf
path, more than 99.8% of the time. Its worst case has length 39; there are eight such
paths, equivalent to the one shown, each obtained with probability 2−
. (And if we
use the modiﬁcation of answer 56, the worst case length rises to 46; there are 40 such
paths, of which the one shown is the most likely — its probability is 2−
. The total
probability of all 40 cases for length 46 is 169
.00000075.)
2 19 4 21
32 1 54 29
43
5 22 1
53 30 33 44 41 28
18 3 20
31 34 15 2 7 10 45 42
23 6
52 21 8 5 12 3 40 27
32 17 30
35 16 23 14 9 6 11 46
7 24 33
38
22 51 20 17 4 13 26 39
34 31 26 9 36 39 28 11
36 49 24 19 38 47
25 8 35 40 27 10 37
18 37 48 25

32 1 42 29
53
43 30 33 52 41 28
31 34 15 2 7 10 51 54
44 21 8 5 12 3 40 27
35 16 23 14 9 6 11 50
22 45 20 17 4 13 26 39
36 47 24 19 38 49
18 37 48 25

46 31 48 1 20 33 50 37
17 44 19 10 5 36 21 34
30 47 16 7 2 9 38 51
43 18 27 4 11 6 35 22
26 29 12 15 8 3 52 39
42 25 28 13 40 23 54

3 36 5
6 43 2
37 4 35
44 7 42 1
41 38 45 34
21 26
8 31 10 39 46 29 18 15
11 40 33 30 13 16 27 20
32 9 12 47 28 19 14 17

2−
·
45 32 49

14 41 24 53

3−

3−

≈

16 13

23

18

21

14

15

13

16

12

29

23

24

25

50

46

22

3

4

18 1
11 8 5 2
17 14 3 10 7
12 9 6 15 4

20

19

≈

≈
≈

60. A tree constructed as in exercise 57 has two diﬀerent forms, depending on whether
, because R6 doesn’t have as much symmetry as R5.
s is a variable of type
(.90, .81, .71, .63, .56) when s = b0.

or
(.86, .74, .65, .57, .50) when s = a0;

a, d

b, c

(a)

{

}

{

}

[For q = 100 these probabilities drop to about .000044 and .000050.]

≈

(b)
(c)

(.06, .05, .05, .04, .04) when s = a0;
≈
((.33, .29, .29, .24, .22), (.26, .26, .24, .19, .17)) when s = a0, t1 = (b0, a1); and

(.07, .05, .05, .04, .04) when s = b0.

((.27, .23, .23, .18, .17), (.28, .21, .18, .15, .13)) when s = b0, t1 = (a0, c0).

≈
62. There are two choices for v2; and the next moves must hug the edge. Thus the
graph reduces either to Pm

1, and we succeed by induction.

1 Pn or Pm Pn

−

−

[It’s necessary to require r = 0; for example, the algorithm can fail when m = n =
4, s = (0, 0), t1 = (0, 3). The start vertex must also be a corner; consider m = 4, n = 5,
s = (0, 2). A similar proof shows that Algorithm W never fails on the convex triangular
grid graphs produced by SGB’s generator simplex (n, n1, n2, n3, 0, 0, 0), when starting
at a corner. It also succeeds on the dual of that graph, provided that n1, n2, n3 < n
and that a suitable starting vertex is speciﬁed; this is the graph whose vertices are the
triangular faces inside the polygon, all of which have degree 2 or 3.]

63. Notice ﬁrst that the standard Gray binary code g(0), g(1), . . . , g(2
1) is one
of the paths that satisfy Warnsdorf’s rule. For example, when n = 3 and s = 000, this
path is 000, 001, 011, 010, 110, 111, 101, 100; and it has the delta sequence δ0 . . . δ6 =
0102010 of the ruler function ρ (see 7.2.1.1–(24)). Warnsdorf’s rule for the 3-cube allows
any δ0
; if δ0δ1 = 01, it forces δ2δ3 = 02; if
0, 1, 2
δ0δ1δ2δ3 = 0102, it allows δ4

; and if δ0 . . . δ4 = 01020, it forces δ5δ6 = 10.

; if δ0 = 0, it allows δ1

∈ {

∈ {

1, 2

0, 1

−

}

}

n

∈ {

}

December 4, 2025

7.2.2.4

ANSWERS TO EXERCISES

71

In general one can prove that if δk

k < r, then Warnsdorf’s
rule allows δr to be any coordinate in the interval Wr = [ρ(r) . . ρ(cid:2)(r)), where ρ(cid:2)(r) =
ρ(r & (r
1)) is the index of the next-to-rightmost 1 in the binary representation of r.
(If r is a power of 2, ρ(cid:2)(r) is undeﬁned; in such cases we use n instead of ρ(cid:2)(r) in the
7, we have ρ(r) = 1 and
formula for Wr.) For example, if r = (1010010)2 and n
ρ(cid:2)(r) = 4, hence Wr = [1 . . 4) =

1 = ρ(k) for 1

1, 2, 3

−

≤

≥

−

.

Moreover, the residual graph of unvisited vertices, when it is time to choose δr, is
always symmetrical with respect to every coordinate in Wr. Therefore we can choose
δr = ρ(r) without loss of generality; all other Warnsdorf paths can be mapped into the
standard path by permuting coordinates. For example, the Warnsdorf paths for the 3-
cube have the delta sequences 0102010, 0102101, 0201020, 0201202, 1012101, 1012010,
1210121, 1210212, 2021202, 2021020, 2120212, 2120121.

{

}

[Algorithm W always succeeds in the graph P3 P3 P3 when s = (0, 0, 0); but
not always in P4 P4 P4. It sometimes fails in P3 P3 P3 P3 when s = (0, 0, 0, 0).]

65. Yes:

. (Is there a smaller one?)

Warnsdorf’s rule
next-to-rightmost 1
Warnsdorf paths
author
random 32-bit weight
long hash code
3-cube
mates

±
2
5

70. It happens when k = t
1 in the ﬁrst call, and when k = 2 in the second call. (A
little time can be saved by detecting these special cases. Similarly, ‘update(u1, . . . , ut)’
1. Such updates weren’t counted in the author’s tests.)
arises in step F5 when k = j

−

71. Let the edges be 1
−−−
1
consider the path 2
−−−

−−−

−−− · · · −−−
3
4
−−−

−−−

n

1 and 1

−−−
(n

2)

−−−

−

−−−

5, 3
3)

−−−

(n

−−−
−

−−−
(n

(n
4)

2), (n
n

−
−−−

−
−−−

−

4)
(n

−−−
1).
−

n;

73. Assign a random 32-bit weight to each edge of the graph, and let each path have
b
). Let there be 2
a “long hash code” H that’s the sum of its edge weights (modulo 2
. If c vertex names can be
hash lists; a path with long hash H will go into list H mod 2
packed into an octabyte, the dictionary entry for (v1, . . . , vt) will occupy B = 1 +
t/c
(cid:24)
octabytes: one for the link and H, the others for the vertices (which are examined in
detail during a search only when the long hash code is correct). Store the qth path in
positions (qB + s) mod M of a large array of octabytes, for 0
s < B, where M is a
large power of 2. (Overﬂow occurs if we try to write into position (p2B + B) mod M .)

≤

32

(cid:23)

b

75. (a) Let H be the graph whose vertices are the Hamiltonian paths of G that start
with v1, adjacent if they diﬀer only by ﬂipping a subpath. Since G is cubic, every vertex
of H has degree 2. So H consists of cycles, and Algorithm F− constructs the cycle that
begins with the given path. For example, when G = P2 P2 P2, we can represent the
vertices (000, 001, . . . , 111) by (0, 1, . . . , 7), and H has two cycles: 01326754
01326457
04513762
04513267

−−−
−−−
01546732

01326754; 04623751

−−−
01573264

−−−
01546247

01375462

02645731

02645137

04576231

02673154

−−−

−−−

−−−
−−−
02376451

−−−

(b) Let α = v1

−−−

−−−
02315467
v2

−−−

02315764

−−−
−−− · · · −−−
−−−

−−−

04675132

−−−

04623157

−−−
04623751.

−−−

−−−
vn be a Hamiltonian path with vn

−−−

−−−

v1. One of
. The

R

its two neighbors in H is v1
other neighbor will have v2 unchanged. So the cyclic paths come in pairs.

v2, which is the reﬂected cycle α

−−− · · · −−−

vn

(c) Consider maximal segments of the cycle in H whose paths begin with v1
v2.
The ﬁrst and last of these paths are Hamiltonian cycles, which we can regard as mates
1 is 01375462.)
of each other. (For example, the mate of 01326754 with respect to 0
(d) If α is a Hamiltonian cycle containing the edge e, its mate β is a Hamiltonian
α. Hence γ, the mate of β with respect to e(cid:2), is a third.
(e) Color the n edges of α alternately red and green; color the other n/2 edges blue.
x of them. Let
−
g green. We have

The blue edges of β and γ are the same; suppose there are n/2
β have r red and g green; hence γ has n/2

cycle containing an edge e(cid:2) /
∈

r red and n/2

−−−

−−−

−

−

December 4, 2025

72

ANSWERS TO EXERCISES

7.2.2.4

r + g + n/2
two consecutive edges of α can appear in β or γ; they must all be the same color.

x) = n; hence x = 0. Therefore no

g) + (n/2

r) + (n/2

x = (n/2

−

−

−

−

[Historical notes: The theorem in (c) was discovered via algebraic reasoning
by C. A. B. Smith, about 1940, but not published until later. See Combinatorial
Mathematics and its Applications (Oxford conference, 1969), 259–283; W. T. Tutte,
Graph Theory As I Have Known It (1998), 18, 48, 94. A. G. Thomason, in Annals of
Discrete Mathematics 3 (1978), 259–268, introduced one-sided ﬂips and used them to
give an algorithmic proof of Smith’s theorem.]
77. (a) Easily veriﬁed. (This is the only non-identity automorphism, when n > 1.)

Historical notes
Smith
Tutte
Thomason
Cameron
Krawczyk
Stappers
generating function
Zhong

(b) Any Hamiltonian cycle containing 05

0
07; hence 03

01 mustn’t contain 0
15, 01

−−−

−−−

06; hence
02, 08

1

−−−

−−−

−−−

−−−

−−−
−−−

04 or 01

08; hence 11

05 but not 05

06
−−−
06, not 02

11 in a graph isomorphic to Cn

07
07
−−−
cycle containing 15
−−−
Similarly, the only Hamiltonian cycles containing 06
08
01

04
−−−
08. Replacing all ‘0j’ by ‘1’ yields a Hamiltonian
1. By induction, it’s αn.
−
06 are
01 and 05
0;
04
0.
03

−−−
−−−
(c) (11, 65, 265, 1005, 3749, 13927, 51683, 191735, 711243).

−−−
−−−
[But an appropriate
sequence of only 4n two-sided ﬂips will take us from αn to βn, or βn to γn, or γn to αn.]

−−− · · · −−−
−−− · · · −−−

βn = 0
γn = 0

−−−
05
04

−−−
15
16

−−−
06
05

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

02
02

07
07

03
08

16
11

01
06

−−−

−−−

−−−

0

0

−−−
−−−

−

−

(d) When n > 2, the ﬁrst ﬁve ﬂips yield 01
17

12

04

15

16

−−−

−−−

03
−−−
that’s the same as the suﬃx 01
to 0
25 and 26. The next cn

−−−

−−−

−−−

11

−−−

−−−

−−−
02

−−−
18 followed by a sequence 21
−−− · · ·
of the second path obtained with respect
13’ appears between
1 ﬂips mimic (c); then six more ﬂips give the reverse of βn.

−−−
−−− · · ·

−−−
22

−−−

−−−

−−−

−−−

−−−

−−−

01, except that all entries are increased by 20, and ‘14

05

06

07

08

02

0

2

2

4

2

2

5

4

3

−

z

−

−

−

−

−

−

2z

2z

2
n

+z

z)(1

+4z

≥
n cnz

1 + 5 in both cases(!), proved as in (d).

(e) When n > 1, the number is cn
[The graphs Cn were introduced by K. Cameron, Discrete Math. 235 (2001), 69–
n
.
77, who simpliﬁed a similar construction by A. Krawczyk and proved that cn
In 2020, Filip Stappers discovered that the generating function c(z) =
is
p(z)/q(z), where q(z) = (1
3z
) and p(z) = z(1 + z)(11 +
z
3
). He also proved that the number of one-sided ﬂips to go from βn to
10z +6z
its mate γn, with respect to either 0
= ˆp(z)/q(z)
and ˆp(z) = 2z(3 + 2z + z
). Consequently the actual limiting ratio cn+1/cn is
8
= 3z
ρ
≈
0.3959. In Bull. Aust. Math.
and ˆcn
∼
Soc. 98 (2018), 18–26, L. Zhong introduced a family of graphs on 16n vertices for which
the number of ﬂips to get from a certain Hamiltonian path to its mate with respect to
0
0 is only 4(!).]
78. (a, b) In contrast to exercise 60, success occurs with probability
100% when
q
10. Furthermore, a Hamiltonian cycle is usually found soon after ﬁnding the ﬁrst
Hamiltonian path. The average number of updates before that ﬁrst cycle, observed in
100 runs for each q, was

3.709398, the real root of z
, where c

10. However, that number with respect to 1

+ 2z
5.349 and ˆcn/cn

+ z + 1. Asymptotically, cn

(81, 141, 146, 240, 295).

+ 2z
ˆp(ρ)/p(ρ)

0, is ˆcn, where

1 is exactly 6

06 or 06

−−−
4

−−−
2

n ˆcnz

−−−

−−−

2z
5

(cid:14)

(cid:14)

ˆcρ

cρ

−

∼

≤

≈

∼

−

≈

−

≈

2

n

n

n

n

·

3

3

But q = 100 was a diﬀerent story. Here a 400-cycle was successfully found in
only six of ten cases — sometimes after as few as 18 thousand updates, sometimes
after as many as 8.3 million. In one of the other cases, millions of Hamiltonian paths
(not cycles) were found; but memory overﬂow, with more than 2 million paths in the
dictionary, aborted the run. Memory overﬂow also arose in the three other cases, once
before achieving any paths longer than 365.

We conclude that Algorithm F can have wildly eccentric behavior, and it should

probably be restarted if it spins its wheels too long.

December 4, 2025

≈

7.2.2.4

ANSWERS TO EXERCISES

73

−−−

(3k+5) for 0

79. (a) Let there be 12 vertices
3k
containing one Hamiltonian cycle and 12 Hamiltonian paths that aren’t cycles.
j < 12, with ik

k < 12 and
k < 4 (modulo 12). This graph has two equivalence classes, each

(k+1) for 0

i < n and

0, . . . , 11

, with k

(b) Let there be 13n vertices ij for 0
k(cid:2) in (a); also i1

≤
i0 and i1

whenever k
equivalence classes, each containing one cycle and 17n noncycles.

ik(cid:2)
n
((i+1) mod n)1. This graph has 2

−−−

−−−

−−−

−−−

−−−

≤

≤

−

≤

{

}

1

80. If and only if s
Murty, Graph Theory (2008), Theorem 18.1.]

≤

t (except when s = t = q1 = 1). [See J. A. Bondy and U. S. R.

Bondy
Murty
isolated vertices
Chv´atal
Bondy
ﬂip
degree sequence
forcibly Hamiltonian
graphical

{

u, v

81. (a) Choose nonadjacent
deg(v) so that deg(u) + deg(v) is
with deg(u)
maximum, and assume that deg(u) + deg(v) < n. Let k = deg(u). Then k > 0, because
there are no isolated vertices when dn
k vertices
1 = n
k, by maximality. Similarly,
= v are nonadjacent to v; these must all have degree
deg(v).
exactly n
t. Hence we have proved

deg(v) vertices are nonadjacent to u, and they all have degree

t if and only if at least s vertices have degree

1. Exactly n

−
But ds

deg(v)

≥

≤

−

−

−

≥

≤

≤

k

}

1

−

that 1

k < n/2, dk
(b) Each Gk satisﬁes (

≤

≤

k, and dn

k

−

deg(v) < n

≤

−

), so Gk+1 exists. Let (w0w1 . . . wn

≤
k, contradicting (

).

∗

≤

that’s not also a cycle in Gk. We can assume that w0 = uk and wn
deg(uk) values of j with w0
because deg(wn

wj+1 in Gk. And wn
−
deg(w0). Thus (w0 . . . wj wn

−
[Condition (

1)
) was discovered by V. Chv´atal, J. Comb. Theory B12 (1972), 163–
168. This proof is due to J. A. Bondy and V. Chv´atal, Discr. Math. 15 (1976), 111–135.]

−−−
1 . . . wj+1) is a cycle in Gk.

−−−

≥

−

n

∗

−

1

−

1) be a cycle in Gk+1
1 = vk. There are
wj for at least one such j,

−

∗

82. Let G(cid:2) be the graph (kK1
0 < j

⊕
k for k < j

k, d(cid:2)j = n

≤

−
83. (a) There are (2r + 1)r/2 edges.

−

≤

Kn
−
n

1

2k)
−−−
k, d(cid:2)j = n

Kk, whose degree sequence has d(cid:2)j = k for
n. (See exercise 80.)

1 for n

k < j

−

≤
(b) Use exercises 2 and 81.

−

−

(c) If u0

uj and uj

1

−

u2r, a ﬂip will create a cycle. So r vertices uj

1 cannot

−

be adjacent to u2r; the remaining r candidates must be u2r’s neighbors.

−−−

−−−

−

−−−

−

u2r
u0

−−−

(d) If the neighbors of u0 are u1, . . . , ur and the neighbors of u2r are ur, . . . ,
1, we have a (2r + 1)-cycle. Otherwise let j be minimum such that u0 /
uj and
−−−
u2r, and we have a 2r-cycle that excludes v0 = uj .

uj+1. Then uj

1

(e) Assuming the hint, we can make a cycle v1
v1 that excludes v2k, for any k; hence v2k

−−−
−−−
−−− · · · −−−
vj for all odd j. But then v1 has
· · · −−−
degree r + 1. [This result was announced in Lecture Notes in Math. 186 (1971), 201.]
Notice that Hamiltonicity is not implied by exercise 81, even though that exercise
is “best possible” according to exercise 82. No eﬃcient way is known to test whether
all graphs with a given degree sequence are forcibly Hamiltonian.

v2k+1

−−−

−−−

v2k

v0

−

1

t

2

−

−

−

(cid:24)

≤

n/2

(cid:23)
≤

1, dn

k = n

, and consider 2

84. Let t =
cases a1 . . . at where a1 = at = 0 and ak =
[dk
+ dn in case
k < t. Then it’s easy to see that the minimum d1 +
k] for 1
1; ak = 1 im-
k = dn
a1 . . . at occurs when k < t and ak = 0 implies dk = k + 1, dn
plies dk = dk
1. (For example, if n = 11 and a1 . . . a6 =
−
010110, we have d1 . . . d11 = 22444677999.) Let s(a1 . . . at) denote this minimum sum.
Suppose j is minimum with aj = 1, and k is minimum with k > j and ak = 0. One
ak . . . at), except that the
ak . . . at) < s(0
1. Consequently the overall minimum
t
t+2
1)t

can show without diﬃculty that s(0
inequality is reversed when n is odd and j = t
sum occurs uniquely for d1 . . . dn = 23 . . . (t
when n > 3 is odd. Increase dn by 1 if the sum is odd.

when n is even, 23 . . . (t

k; also dn = dn

−
1)t

· · ·
k
−

1)(t

−

−

−

−

1

−

−

−

−

−

k

k

1

1

j

j

The resulting sequence of degrees is graphical, by exercise 7–105. Hence the answer
3)/16(cid:17) when n is odd.

+ 6n)/16(cid:17) when n is even; (cid:16)(3n

turns out to be (cid:16)(3n

+ 8n

2

2

−

December 4, 2025

(cid:12)
74

ANSWERS TO EXERCISES

7.2.2.4

t

f (n, k+1) if and only if k <

≥
t<n/2 f (n, t). Every graph (tK1

Kn
2t
n
⊕
−
t)
−
2
t has at most t
edges that don’t. Hence a graph with d1

85. The quadratic function f (n, k) satisﬁes f (n, k)
Thus g(n, k) = maxk
≤
is non-Hamiltonian, with degree sequence t
Furthermore, every graph with dt
vertices and at most
g(n, k) edges must have dt > t for k
[Magyar Tudom´anyos Akad´emia Matematikai Kutat´o Int. K¨ozl. 7 (1962), 227–228.]
86. Every graph ((t + 1)K1
−−−
So we can achieve ˆg(n, k) = max(f (n, k), f (n,

1
−
3 .
t < n/2
≤
and f (n, t) edges.
edges that involve its ﬁrst t
k and more than
t < n/2. And exercise 81 calls it Hamiltonian.

1)/2, is untraceable.
.
k <
(cid:17)
On the other hand, by exercises 2 and 81, a graph is traceable whenever its degree

≤
−
1)) edges, when 0

Kt for k
t
−−−
1)

Kt, for k
n/2

t < (n

−
(n

n/2

(cid:17) −

2t)

Kn

2t)

(n

⊕

≤

≤

≥

−

−

≤

−
2

1

(cid:15)

(cid:16)

(cid:16)

(cid:16)

−

−

n

n

1

t

degree sequence
components

sequence d1

dn satisﬁes the following condition:

≤ · · · ≤
1

≤

t < (n + 1)/2 and dt < t implies dn+1

t

−

t.

n

−

≥

(+)

s

n

≤

−

≤

≤

−

t; ds

≤
−

t; and ds

1 for n + 1

n + 1
1)

n/2
(cid:17)
1 for 1

ˆg(n, k). (The last inequality holds because k

is always traceable. If k <
1 for

In particular, a graph with minimum degree d1
≥ (cid:16)
t
and (+) fails for some t, we have ds
n/2
−
(cid:16)
(cid:17)
t < s
t < s
≤
ˆf (n, t
−
88. (a) Let v0
vl be a longest path, and assume that l < 2k. We will prove
ﬁrst that there’s actually an l-cycle, using the fact that all neighbors of v0 and vl must
lie on that path. Indeed, let
be the neighbors of vl. Then I and J are subsets of
because
v0

be the neighbors of v0, and let
1, . . . , l
I

vj
}
. They can’t be disjoint,
}
J; and we have the cycle

{
k. Therefore there’s some j
v0.

≤
≤
n. Hence (d1 +

−
−
+ dn)/2
1.)

J
|
vl
But there can’t be an l-cycle! Since l

| ≥
−−−· · · −−−

k and
1

−−− · · · −−−

−−− · · · −−−

· · ·
(cid:17) −

| ≥
vj

n/2

≤ (cid:16)

−−−

−−−

vj

≤

≤

≤

−

vi

∈

∩

∈

∈

n

J

{

}

1

{

I

I

−

−

j

t

t

i

|

|

|

1

2 and G is connected, there must be ver-
w(cid:2) for some j. So there’s a longer path.

tices w and w(cid:2) not on the cycle, with vj
(b) The result clearly holds for n

l + 1, because the number of edges is

≤
nl/2. Also for larger n, if G isn’t connected; for if there are r components, with nj
vertices and mj edges in component j, each nj is less than n. By induction, the number
m1 +

+ mr of edges is at most (n1 +

+ nr)l/2 = nl/2.

≤

(cid:15)

(cid:16)

n
w

−
−−−

≤
−−−
≤

n
2

Assume therefore that n > l + 1 and G is connected. Let k =

+ 1. Then
2k > l, so there’s no path of length 2k. Hence by (a), there’s a vertex v of degree < k,
unless n = 2k = l + 2. And v exists even in that case; otherwise exercise 81 tells us
there would be a cycle of length 2k, hence a path of length 2k

l/2

(cid:16)

(cid:17)

· · ·

· · ·

Now G
(c)

v has at most (n
Kl+1

n/(l + 1)

\

−

(cid:16)

(cid:17)

⊕

−
1)l/2 edges; so G has at most (n

Kn mod (l+1), a graph with

same number of edges is achieved by the much more interesting graph Kl/2
if l is even and n > l and n mod (l + 1)

l/2, l/2 + 1

!)

−−−

−
n/(l + 1)
(cid:24)

(cid:23)

1 > l.
1)l/2 + k

nl/2.
1
−
components. (The
l/2,

K n

≤

−

∈ {

}

89. (a) Let l be the length of G, and consider a longest path v0
vl
where vl
p;
so we assume that c < 2k. A vertex vq will be called “bounded” if its neighbors all
belong to the cycle. We shall prove that vq is bounded whenever p < q

vp and p is as small as possible. The resulting cycle has length c = l + 1

−−− · · · −−−
−

−−−

−−−

v1

l.

{

=

The idea will be to construct a longest path v0

v(cid:2)l,
and v(cid:2)l = vq. Then vq must be bounded, because

−−− · · · −−−

−−− · · · −−−

v(cid:2)p+1, . . . , v(cid:2)l

vp+1, . . . , vl

where
l is maximum and p is minimum. Vertex vl is clearly bounded; so is vertex vp+1.
and
I
∈
k.
J
,
|
|
1 . . . vp+1vi . . . vq.

Suppose vq+1 is bounded, and let the neighbors of vp+1 and vq+1 be
j
∈
If i

vi
, where we set vl+1 = vp. Also

J, let vpv(cid:2)p+1 . . . v(cid:2)l = vl+1 . . . vq+1vi

J
∪
q and i

. Then I

}
| ≥

i
|
I
|

−−−

vp

vj

J

}

{

}

}

{

{

|

−

≤
v(cid:2)p+1

}
I and i
≤
I and q < i

∈

If i

∈

December 4, 2025

vp+1, . . . , vl+1
⊆ {
1
−
l and i + 1

∈

∈

≤

J, let vpv(cid:2)p+1 . . . v(cid:2)l = vl+1 . . . vi+1vq+1 . . . vi

−−−

articulation point
components
articulation point
bicomponent
traceable
Historical notes
Erd˝os
Gallai
Faudree
Schelp
Woodall
cubic graphs
perfectly Hamiltonian
Coxeter
miracle

7.2.2.4

ANSWERS TO EXERCISES

75

\

∪

vp+1 . . . vq. One of these constructions must work; otherwise we’d have ruled out at
least k

1 of the c potential elements of J, and we also have q + 1 /
∈
vp+1, . . . , vl

can’t all be bounded! If p = 0, the graph G would be discon-

−
But

J.

nected; otherwise vertex vp would be an articulation point.

{

}

−

≤

c, because the number of edges is

(b) The result clearly holds for n
≤
(n
1)c/2. Also for larger n, if G isn’t connected; for if there are r components, with
nj vertices and mj edges in component j, each nj is less than n. By induction, the
number m1 +
1)c/2.
Assume therefore that n > c and G is connected. If G isn’t biconnected, there’s an
articulation point v that divides G into a bicomponent G(cid:2) containing v and a connected
graph (G

v. If G(cid:2) has n(cid:2) vertices, G has

+ mr of edges is at most ((n1

n(cid:2))c/2 edges.

1))c/2 < (n

1)c/2 + (n

+ (nr

1) +

G(cid:2))

(n(cid:2)

· · ·

· · ·

≤

−

−

−

(cid:15)

(cid:16)

n
2

Finally, assume that G is biconnected and n > c. The proof follows as in exercise

1

−

−

−

(cid:17)

(cid:16)

(cid:16)

(

−

⊕

(n

Kc

c/2

−−−

K(n

1)).

1) mod (c

1)/(c

(c) K1

1) mod (c
−
(n

1) in a row, then paste them together;

−
edges is achieved by a traceable graph: Put
K1+(n

88(b), because there exists a vertex whose degree is less than k =
1)

+ 1.
(The same number of
copies of Kc and a
if (n, c) = (12, 4).)
Historical notes: These results and those of the previous exercise are due to
[Acta Mathematica Academiæ Scientiarum Hungaricæ 10
P. Erd˝os and T. Gallai
(1959), 337–356]. R. J. Faudree and R. H. Schelp [J. Combinatorial Theory B19 (1975)
150–160] proved that the lower bound of exercise 88(c) is sharp: The upper bound in
88(a) can be replaced by the size of those graphs. Similarly, D. R. Woodall [Acta Math.
Acad. Sci. Hung. 28 (1976), 77–80] proved that the lower bound in (c) is sharp.

−
1)/(c

1)

−

−

(cid:17)

(cid:16)

(cid:17)

90. True, except when G has no edges (and length 0). See exercise 2.

93. (a) True, unless there are fewer than 4 vertices.

(b) Graphs like

and

for n = 9 and n = 10 work in general.

≤

−

−

[Mathematical Gazette 49 (1965), 40–41. These cubic graphs for even n are also
(k + 1) and

perfectly Hamiltonian. A more symmetrical graph, whose edges are k
(k + n/2) (modulo n), can also be used when n is a multiple of 4.]
k

−−−

−−−

95. (a) Powers of the “obvious” permutation σ = (a0a1a2a3a4a5a6)(b0b1b2b3b4b5b6)
(c0c1c2c3c4c5c6)(d0d1d2d3d4d5d6) will take d6
dj for any j. There’s also a “sur-
prise,” ρ = (a0b0)(a1b2)(a2d2)(a3c2)(a4c5)(a5d5)(a6b5)(b1b6)(b3d6)(b4d1)(c1d4)(c6d3);
one can verify that uρ
v. (Notice that c0, c3, c4, and d0 are
ﬁxed by ρ. Coxeter called this “an apparent miracle.”) When ρ is premultiplied and
postmultiplied by appropriate powers of σ, we can take d0 into any desired vertex.

vρ whenever u

−−−

−−−

(cid:4)→

(cid:4)→

b5j , bj

The mapping aj

d5j , namely the permutation
(cid:4)→
τ = (a0b0c0) (a1b5c4a6b2c3) (b1c5a4b6c2a3) (c1a5b4c6a2b3) (d1d5d4d6d2d3), is another
automorphism that ﬁxes d0. When d0 is ﬁxed, we must take its neighbor c0 into a
2
neighbor; hence we can let S26 =
. And when c0 is also ﬁxed, we can let
S25 =

(), τ, τ
, because b0 must map to itself or a0. Clearly S24 =

a5j, dj

c5j , cj

(), ρ

(cid:4)→

(cid:4)→

()

}

{

.

Finally, can we move anything else when d0, c0, b0, a0 are all ﬁxed? Aha — there’s
j,

, which swaps aj

j , dj

j, cj

3

c−

↔

d−

↔

just one possibility, namely τ
for 0 < j < 7. Thus S23 =

(), τ

3

(b) Part (a) explains how to map v
w(cid:2).
(c) In fact, part (a) shows that u
−−−
(d) Algorithm H quickly shows that there are no Hamiltonian cycles. But there

· · ·
(cid:4)→
w can be mapped to any u(cid:2)

(cid:4)→
v

−−−

−−−

−−−

v(cid:2)

{

}

{

and S22 =
d0

↔

a−
j, bj
= S1 =
v(cid:2).

b−
.

↔
()
}

are 12 cycles, such as a1

a0

a6

a5

a4

a3

a2

d2

c2

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

c6

−−−

December 4, 2025

{

}

{

}

76

ANSWERS TO EXERCISES

7.2.2.4

−−−

{

c4

c3

b0

b4

b5

b2

d3

d5

d4

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

d6
c5

b1
d1

−−−
−−−

−−−
−−−

−−−
−−−

0, 1, 2, 3, 4, 5, 6,

b3
c0
−−−
a1, that omit (say) d0.

b6
c1
Historical notes: The Coxeter graph was ﬁrst discussed in print by W. T. Tutte
[Canadian Math. Bulletin 3 (1960), 1–5], who proved it non-Hamiltonian. Eventually
H. S. M. Coxeter wrote about “his graph” [J. London Math. Society (3) 46 (1983),
117–136], identifying its vertices with the
of the set
. His new names for vertices a0 through d7 were respectively
D =
25, 36, 04, 15, 26, 03, 14; 34, 45, 56, 06, 01, 12, 23; 16, 02, 13, 24, 35, 46, 05; 0
,
∞
x < y < 7, the neighbors
, 3
2
∞
≤
of xy are
, using arithmetic
,
4x + 4y,
−
−
mod 7. He showed that the 7
7 = 336 automorphisms correspond to the mappings
, where f is a fractional linear transformation on D; that is,
= 0 and either
) = a/c.

f (x), f (y)
{
f (x) = (ax + b)/(cx + d), where 0
c = 1 or (c, d) = (0, 1). (In this computation, x/
The automorphisms σ, ρ, τ above correspond respectively to f (x) = x + 1, 1/x, 5x.)

(abbreviating
2y

by xy). If 0
, and
2x

= 28 unordered pairs

a, b, c, d < 7 and (ad

, 6
∞
y, 3x

= 0, x/0 =

bc) mod 7

, and f (

∞
2x
{

∞
−

{
x, 3y

} (cid:4)→ {

}
−

x, y

x, y

x, y

∞}

∞}

, 5

, 4

, 1

∞

∞

∞

∞

∞

2y

≤

−

−

3
{

8
2

}

}

{

}

}

{

(cid:16)

(cid:15)

Historical notes
Tutte
Coxeter
fractional linear transformation
Beluhov
generating functions
ternary sequences
bipartite
Historical notes
Demoucron
Malgrange
Pertuiset
Bader
printed circuits
blocks
biconnected components

∈

∈

−−−

sj+1

vj+1

wj+1

C ] + [wj

100. (Using ideas of N. Beluhov.) When C is a cycle cover, let sj = 4[tj
2[vj
−−−
modulo q. A simple case analysis shows that sj
5, 6
sj = 3 =
sj = 7 =
1, 2, 4

C ] +
C ] encode its edges between indices j and j + 1
sj+1 = 7;
;
; sj = 5 =
}
}
}
; and that the sequence s1s2 . . . sq completely determines C.
}
Thus there are two kinds of covers: Type A, where sj is alternately 7 and an
element of
. Type A covers
arise only when q is even, and they have k + 1 cycles when there are k occurrences of
sj = sj+2

= 7. Type B covers always have exactly 2 cycles.

; or type B, where each sj is an element of

1, 2, 4
}
; sj = 6 =
⇒

= 0; sj
3, 5

⇒
⇒

⇒
sj+1

1, 2, 4

3, 5, 6

sj+1

sj+1

tj+1

∈ {

∈ {

∈ {

∈ {

−−−

3, 6

∈ {

⇒

=

∈

}

{

{

}

[a0=a1]+

+[an−1=an]

n

···

z

w

(cid:14)

Let g(w, z) =

[a0 = an ], summed over all ternary se-
= an. Then g(w, z) =
quences a0a1 . . . an, and let h(w, z) be similar but requiring a0
3+wzg(w, z)+zh(w, z) and h(w, z) = 2zg(w, z)+(1+w)zh(w, z). So we ﬁnd g(w, z) =
3(1
(2 + w)z).
] g(w, z) =
Consequently the number of type A covers with k cycles is 2 [w
4
) when q is even. (In particular, the number of Hamiltonian
(cid:16)
).)
cycles is 4(2

1)z) + 1/(1
k
z

(w + 2)z)) = 2/(1

(1 + w)z)/((1

1)
−
+ (

−
q/2
1
k

1)z)(1

−
k

−
q/2

−
−

(w

(w

1)

(2

(
1

q/2

q/2

q/2

q/2

−

−

−

−

(cid:15)

−

−

−

−

k

1

Turning to type B, let there be fxyn sequences a0 . . . an with a0 = x, an = y,
, having no consecutive 33 or 56 or 65. We ﬁnd by induction
)/3 + δxyn, where δxyn = 1 when n is even and x = y,
1)
, otherwise δxyn = 0. Hence there are

3, 5, 6
and each aj
n
}
∈ {
that fxyn = (2
(
−
δxyn =
1 when n is odd and xy
q
f33q + f55q + f66q = 2

+ 2[q even] covers of type B.

33, 56, 65

∈ {

−

−

}

n

−

−−−

−−−

vn = v0. Every edge of G

v1
vj for some 0

103. Let H = v0
H has the form
−−− · · · −−−
i < j < n. When G is drawn in the plane with no crossing
eij = vi
≤
(cid:0)
with i < i(cid:2) < j < j(cid:2) cannot both lie inside H, nor can
edges, two edges eij and ei
j
they both lie outside H. Therefore the graph E whose vertices are the eij, with eij
when i < i(cid:2) < j < j(cid:2), must be bipartite. Conversely, if E is bipartite,
adjacent to ei
G is clearly planar. (And bipartiteness is readily tested by Algorithm 7B.)

\

j

(cid:0)

(cid:0)

(cid:0)

Historical notes: This criterion for planarity was discovered by G. Demoucron,
Y. Malgrange, and R. Pertuiset [Revue Fran¸caise de Recherche Op´erationnelle 8 (1964),
33–47] and independently by W. Bader [Archiv f¨ur Elektrotechnik 49 (1964), 2–12], at
the time when planarity of printed circuits began to be important. A graph is planar if
and only if its blocks (biconnected components) are planar; and in practice, a block that

December 4, 2025

(cid:12)
(cid:12)
(cid:12)
(cid:12)
K5
K3,3
2-colorable
cyclic permutation
NAME(v)
purge(w, v)
complete tree
rotations
binary trees
associahedron
“net” graph

7.2.2.4

ANSWERS TO EXERCISES

77

isn’t a single edge is almost always Hamiltonian. Notice that the nonplanar graphs K5
and K3,3 have Hamiltonian cycles, and the corresponding graphs E aren’t 2-colorable.
105. (a) [n

where π is a cyclic permutation.

3]n!/(2n), one for every pair

π, π−

≥

(b) [m = n

2]n!

2
/(2n).

≥

{

}

14

24

−−−

−−−

08
27 .
06

106. [This problem is scheduled to appear in the American Mathematical Monthly, so
the answer is “embargoed” until the deadline for reader submissions has passed.]
108. (a) Those are the only remaining ways to include vertex 28 in the cycle.

08
16 would form a short cycle; so 08 must be covered by
06
14 and

(b)
(c) 14 must be covered by
(d) We must choose
25 and 05

14
26 ; but then 26
14
22 to avoid the contradiction, after which
16 as the only ways to cover 04 and 24. Then

18
−−−
−−−
03
15 leaves 23
−−−
07
04
15 is forced,
and almost everything is nailed down. Hence there are two ways to complete a cycle
after the choices of (a), (b), and (d): either
109. (In this graph we have NAME(0) = 00, NAME(1) = 01,
MATE(0) is
0; MATE(1) = 21; MATE(2) = 22; MATE(3) = 23; MATE(4) =
111. TRIG needs at most n locations, because no vertex can be a trigger more than
once (when its degree drops to 2). ACTIVE needs at most
locations, because
at most n
slots, where each
“slot” holds a mate and a degree, because there can be at most n levels.
112. (a) activate(u); activate(w); remarc(u, v); remarc(w, v); and makemates(u, w).

l vertices are outer in level l. SAVE needs at most n
(cid:16)

. . . , NAME(29) = 29.)
1.

n+1
2

05
26 ,

06
25 ,

05
13 ,

06
14 ,

−−−

−−−

−−−

26.

14
26

13
25

or

≥

−

−

{

}

{

}

(cid:15)

.

2

(b) activate(u); remarc(u, v); purge(w, v); makemates(MATE(w), u); deactivate(w).
Here ‘purge(w, v)’ means ‘remarc(NBR[w][k], w) for k decreasing from DEG(w)
1 down
to 0, except when NBR[w][k] = v’; it removes w from the lists of its non-v neighbors.
(c) activate(w); remarc(w, v); purge(u, v); makemates(MATE(u), w); deactivate(u).
(d) Do nothing if e = n. Otherwise purge(u, v); purge(w, v); makemates(MATE(u),

−

k < n. Then do this for 0

≤
EV[k]. If x[EV[k]] < 0, set x[EV[k]]
←
k
≤

k < n: If x[EU[k]] < 0, set
EU[k];
n set

x[0], and for 3

0, v2

←

←

≤

≤

←

← −

1 for 0

EV[k]; else set y[EU[k]]

MATE(w)); deactivate(u); deactivate(w).
113. Set x[k]
x[EU[k]]
else set y[EV[k]]
vk
1]? y[vk
(vk
115. Assume that n > 4. The root has degree n
is T (n
−
T (d0, . . . , dr
−
(The kth subtree has (n

EU[k]. Finally set v1
1]: x[vk

2 = x[vk

←
−

1]).

←

←

−

1

1

−

−

−

−

3, n

2, . . . , 2); and the last subtree is T (n

k, n
1) denotes the complete tree with dl-way branching at level l for 0
3)! of the (n

1)!/2 solutions.)

k)(n

3, n

−

−

−

≤

−

−

−

−

2. The kth subtree, for 1

−

≤

k < n
2,
2, . . . , 2). Here
l < r.

−

116.

|

k(G

is one of the six ways to do 14 suitable rotations of those binary trees. (These are
also the Hamiltonian cycles of an associahedron; see exercise 7.2.1.6–29.)
117. (a) True. (t(G) = 0 if and only if U =
U )

=
1 (and the term for this U leaves the ‘min’ if k(G

(b) If
U
|
U ) = k(G
\
(c) This follows from the monotonicity proved in (b), since t(Cn)
(d) After cutting out m(cid:2) vertices of the smaller part and n(cid:2) vertices of the larger
part, the residual graph that’s left is connected unless m(cid:2) = m or n(cid:2) = n. The smallest
ratio (m(cid:2) + n(cid:2))/(m

n(cid:2)) is m/n in such cases. (See exercise 105.)
(e) 4/3, by cutting 4 independent vertices. (Let N be the “net” graph,

\
U ) = 1).
\
1.
≥

U ), edge e joins two components of G

disconnects G.)

/k(G
\
U )
e

e; hence

m(cid:2) + n

/k(G

−

−

−

U

\

\

∅

\

\

e

|

|

; the
N. A 42-vertex non-Hamiltonian graph

smallest non-Hamiltonian tough graph is K1

−−−

December 4, 2025

(cid:12)
Bauer
Broersma
Veldman
Chv´atal
gadget
Fleischner
Frucht graph
automorphisms
identity
historical notes
Halin

78

ANSWERS TO EXERCISES

7.2.2.4

with t(G) = 2 was (surprisingly) constructed by D. Bauer, H. J. Broersma, and H. J.
Veldman, in Discrete Applied Math. 99 (2000), 317–321; it’s tough for Algorithm H!)
Kt; graph D in Table 1 is the special case
t/(t + 1); hence Nt,m is non-tough. Chv´atal’s original paper

N5,3. We have t(Nt,m)
about toughness appeared in Discrete Mathematics 5 (1973), 215–228.)

(Let Nt,m be the graph (t+1)Km

−−−

≤

|

×

W1

(V1

|
×

= m and

W
|
W )

118. (Solution by V. Chv´atal.) Let the vertices of G = Km Kn be V
= n. Given p > 1, the smallest set U that makes k(G
V
|
the form (V
∪ · · · ∪
\
are set partitions of V and W. Hence
Wj
= mj and
Vj
|
when m1 = m + 1
the smallest such
t(G) = min

W, where
×
U ) = p has
\
Wp), where V1
Vp and W1
Wp
mpnp, where the sizes
m1n1
= mn
= nj are positive integers that sum to m and n. It is minimized
p, and all other mj and nj are 1; in other words,
p, n1 = n + 1
p). Hence
is mn

|
−
U
|
|
min(m,n)
(p
p=2

119. They take v
(31, 19, 21, 16), and (31, 21, 19, 16). (We have 1/

−
av+b
cv+d ) mod 47, where (a, b, c, d) = (20, 15, 17, 27), (20, 17, 15, 27),
(
a
= 0, 1/0 =
c mod 47.)

−
p)/p = (m + n

−
−
1)(m + n

∪ · · · ∪
− · · · −

Vp
×
U
|

1)(m + n

−
2)/2.

p)(n+1

p) = (p

∪ · · · ∪

(m+1

, and

−
1)

(cid:4)→

(p

−

−

−

−

−

−

|

|

|

∞

∞

∞ (cid:4)→

i
i

j
j

v
V

u
U

Z
x

U
u

y
X

V
v

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

(b) Since G

120. (a) The automorphisms are generated by (i, j, k, u, v, w, x, y, z, U, V, W, X, Y, Z)
(cid:4)→
(j, k, i, V, W, U, X, Y, Z, v, w, u, z, x, y) or (i, j, k, U, V, W, Z, X, Y, u, v, w, y, z, x). The cy-
x
k
cles x
−−−
−−−
and Z
Z
k
−−−
−−−
are quickly found by Algorithm H (just 50 nodes in the search tree).
(t)

−−−
−−−
(t)
0 has a unique Hamiltonian path from x

to X
uses it as a “gadget” to prevent any of the edges between Qt and G
any Hamiltonian cycle of Gt. The proof relies on the fact that qt

, this construction
from appearing in
Pt.
(See H. Fleischner, J. Graph Theory 75 (2014), 167–177, Lemma 1. He goes on
to deﬁne G4 and G5, thereby removing the degree-3 vertices Y and z in a similar way;
those reductions introduce many more cycles, yet only one of them includes the edge
U. Another trick removes y and Z, in a graph G6 that’s half of his tour-de-force!)
u

−−−
−−−
(t)

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

−−−
−−−

(t)
0
pt

W
w

w
W

X
y

−−−

−−−

−−−

−−−

Y
z

z
Y

Qt

qt

122. (a) For example, the triangles
how to the triangles

A, B, J

,

{
F, G, H
}

b, e, f
,

,
{
}
C, D, L
}

{

,

g, k, l
. Hence the other vertices

must correspond some-
and

d, i, j

a, c, h

}

{

}

{
must also correspond to each other in some order. The solution is

{

}

{

}

−−−

E, I, K

}

{

(a, b, c, d, e, f, g, h, i, j, k, l)

↔

(I, J, K, H, A, B, L, E, F, G, C, D).

[It’s unique, because this happens to be the “Frucht graph,” one of the smallest
cubic graphs that has no automorphisms except the identity. See R. Frucht, Canadian
J. Math. 1 (1949), 365–378. Halin graphs were introduced by R. Halin, Combinatorial
Mathematics and its Applications (Oxford conference, 1969), 129–136.]

−−−

−−−

−−−

−−−

−−−

0, 2

5, 5

(b) For each nonleaf of T except the root, introduce the chord i

((j +1) mod q)
when its descendant leaves are xi . . . xj. (The chords for b, c, d, g in the example are
4, because x0 . . . x6 = efklhij.)
0

2, 2
(c) Choose any region to be the root. The other regions and sides will form a
tree T , when we ignore the adjacencies between sides of C, because the other adjacencies
form no cycles. The children of each region in T are its adjacent regions and sides,
except for the parent, in (say) clockwise order. For instance, if we choose root I in the
example, the children of I might be (J, K, H); the children of J are (A, B); the children
of K are (L, E); etc.; we could also have decided to let the children of I be (K, H, J) or
(H, J, K). Or we could have chosen root K, with children (E, I, L) or (I, L, E) or (L, E, I);
then the children of I would be (H, J), etc.

December 4, 2025

8 knight graph

Howroyd
OEIS
Skupie´n
Holzmann
Harary
historical notes
8
×
Kocay
pruning the search
articulation point
Hopcroft
Tarjan
depth-ﬁrst
bicomponents
Stanford GraphBase

7.2.2.4

ANSWERS TO EXERCISES

79

n

≤

123. The answers for 4
16 are 1, 1, 2, 2, 4, 6, 13, 22, 50, 106, 252, 589, 1475,
computed by using deﬁnition (ii). See A. Howroyd, OEIS A346779 and A380362 (2025).
124. By induction on the size of T in exercise 122(i). The result is clear when tree T has
2 children u1 . . . ud, all leaves.
depth 1. Otherwise some nonroot vertex v

∈
Case 1: d > 2. Let H0 be the Halin graph obtained by deleting leaf u2. Then

T has d

≤

≥

H0 has the subgraph

v

u1

u3

where H has the subgraph

v

.

u1

u2

u3

Since u2 has degree 3, the Hamiltonian cycles of H have three possible forms:

u2

v

−−−

−−−

α

−−−

u1

−−−

u2,

u2

v

−−−

−−−

α

−−−

u3

−−−

u2,

u2

u1

α

−−−

−−−

−−−

u3

−−−

u2,

where the middle part is a Hamiltonian path of H0. And such paths in H0 arise from
u3. So
u3, u1
u1, v
Hamiltonian cycles that respectively include the edges v
H has cycles that include/exclude u2
v. Furthermore, a Hamil-
u3, u2
tonian cycle of H0 that excludes u1
u3; so we obtain
−−−
u3, and the edges from u1
Hamiltonian cycles in H that include/exclude v
and u3 to their anonymous neighbors. It’s easy to include/exclude the other edges.

−−−
u1, u2
−−−
−−−
u3 must include u1

−−−
−−−

u1, v

−−−

−−−

−−−

−−−

−−−

v

Case 2: d = 2. Now obtain H0 by changing v to a leaf; in this case

H0 has the subgraph v where H has the subgraph

u0

u1 u2

, letting u0 = v.

−−−

−−−

j97 = 58

By threefold symmetry, the Hamiltonian cycles of H that avoid edge ui
uj corre-
spond precisely to the Hamiltonian cycles of H0 that avoid the “opposite” edge from v.
[Considerably more is also true; see Z. Skupie´n, Contemporary Methods in Graph
Theory (Mannheim, 1990), 537–555. Uniform Hamiltonicity was introduced by C. A.
Holzmann and F. Harary in SIAM J. Applied Math. 22 (1972), 187–193.]
125. i97
54 = π78004π78005
127. GA is impossible, because the arcs AL
128. C, H, P , and U . (See exercise 103.)
129. (In the modiﬁed step H11, we can terminate the loop immediately if we encounter
a vertex of degree 0 or 1.) The modiﬁed algorithm works surprisingly well: It wins
convincingly on graphs A, G, and U (58 Mμ, 2762 Gμ, and 27 Gμ); it ties or does
slightly better on graphs C, H, and T . It’s slightly slower on graphs B, P , and Q; and
it’s more than 25% slower on graphs D, E, F , R, S.

NC are forced.

π78006π78007.

GA and GA

−−−

−−−

−−−

−−−

−−−

−−−

FL

SC

×

On the 8

8 knight graph, min-remaining-values takes about 6.0 petamems to

ﬁnd all 13 billion solutions, compared to 6.7 petamems for max-remaining-values.
130. In other words, if the present state of the computation can lead to a Hamiltonian
cycle C, the current graph G(cid:2) must have a Hamiltonian cycle C (cid:2). Indeed, that C (cid:2) can
be exhibited by replacing each subpath in C by the corresponding virtual edge of G(cid:2).
(Conversely, every Hamiltonian cycle of G(cid:2) that actually uses every virtual edge
corresponds to a unique Hamiltonian cycle C of G. There might, however, be other
Hamiltonian cycles in G(cid:2). This graph G(cid:2) was deﬁned by W. Kocay in his paper of 1992,
but he doesn’t seem to have realized its full potential for pruning the search.)

One can, for example, discover whether or not G(cid:2) has an articulation point by
using Hopcroft and Tarjan’s eﬃcient depth-ﬁrst algorithm for bicomponents (Algo-
rithm 7.4.1.2B, or BOOK COMPONENTS in The Stanford GraphBase).

December 4, 2025

80

ANSWERS TO EXERCISES

7.2.2.4

133. No! Let C be a cycle (0, 0) = v0
v is
vn
in C if and only if uα
vα is also in C, where (i, j)α = (j, i) denotes reﬂection about
the main diagonal. Let k > 0 be minimum with vk on the diagonal; that is, vk = vkα.
Then vk+1 = vk
vkα is the other edge of C that touches vk.
, and only two
Similarly, vk+2 = vk
elements of the diagonal are in C. Contradiction.

2α, and so on; we ﬁnd v2k = v0. Hence 2k = n

1α, because vk

2 = (0, 0) for which u

−−− · · · −−−

−−−

−−−

−−−

−−−

1α

v1

−

−

−

2

The same argument shows more generally that no nontrivial automorphism α of

a rectangular board can be a symmetry of a knight’s cycle when α has ﬁxed points.

central symmetry
Jelliss
Bergholt
Euler
Hamiltonian paths

1

−

−

i, j), and let the cycle begin (0, 0) = v0

−
1, 0). Notice that m is even; otherwise ((m

134. Let (i, j)α = (m
vk =
(m
1)/2, 0) would be a ﬁxed point of α.
Therefore k is odd. Case 1: v1α = vk+1. Then vk+2 = v2α, . . . , and v2k = vkα = v0.
So mn/2 = k is odd. Case 2: vk
k = 2l + 1.
1 = v1α. Then vk
But we can’t have both vl+1

−
vl and vl+1 = vlα.

j = vj α for 0

−−−· · · −−−

−−−

v1

−

≤

≤

−

j

[Similar conditions apply to central symmetry, as we’ll see in exercise 136. These

−−−

results are due to G. P. Jelliss, Chessics 2, 22 (Summer 1985), 64.]

135. Let graph G have N = mn/2 vertices, one for each pair
cells; here 0

y < n, and ¯x = m

≤
for all knight moves xy

xy, ¯xy

in G are

}

≤

x < m/2, 0
x(cid:2)y(cid:2), ¯x(cid:2)y(cid:2)

{

}

{
0
≤
and

y(cid:2) < n. (For example, when m = 10 we have

{

}

{

}

.)

=

51, 41
41, 51
00, ¯00
Given a Hamiltonian cycle
there’s a unique knight path 00 = x0y0
0
knight’s cycle by deﬁning xN+kyN+k = ¯xkyk for 0

}
−−−

= v0

x1y1

≤

≤

k

{

−−− · · · −−−

k

≤

≤

N .

}

of equivalent
xy, ¯xy
{
x. The neighbors of
x(cid:2) < m and
51

1
x(cid:2)y(cid:2) with 0
41, 51

≤
, since 30

−

−
−−−
30, 60

{

} −−− {

}

−−−

v1

−−−

−−− · · · −−−

vN =
xN yN with xkyk

{

00, ¯00

}
∈

in G,
vk for
n

×

N . We must have xN yN = ¯00, because N is odd. Therefore we get an m

136. We’ll need names for these two kinds of symmetry. The right-hand species of
symmetry is called Bergholtian, because it was discovered by Ernest Bergholt [British
Chess Magazine 38 (1918), 104, 195; see also The Games and Puzzles Journal 2, 14
(16 December 1996), 234]. The left-hand species is called Eulerian, because Leonhard
Euler gave many examples of such cycles in

34 of his 1759 memoir.

{
are, similarly, the vertices

§
As in answer 135, we deﬁne a graph G with N = mn/2 vertices; but this
time the vertices represent pairs
y). The
−
neighbors of
xy, xy
obtained from knight moves
xy
x(cid:2)y(cid:2). Now, however, there’s a slight problem: There are two “self-loops,” because
we can have xy
u1, where
−−−
3
n
m
−
.) It may seem best
2 ), (
u0 =
(
(
{
to simply disallow those self-loops; after all, a self-loop can’t be in a Hamiltonian cycle.
But further analysis reveals that the Bergholtian solutions correspond precisely

x(cid:2)y(cid:2). (More precisely, we have u0
m
2 ), (
2 )(

, where xy = (m

u0 and u1
n

and u1 =

x(cid:2)y(cid:2), x(cid:2)y(cid:2)

2
−
2 )(

2
−
2 )(

−−−
m
2 )(

xy, xy

3
−
2 )

x)(n

2 )

25–

−−−

−−−

n+1

n+1

−

−

−

}

}

}

{

{

1

1

{

}

}

m

§

to the Hamiltonian paths between u0 and u1. Indeed, from a path u0 = v0
vN
m
(
a Bergholtian cycle.

1 = u1 in G, we get x0y0
−
2
−
−
2 ). Then x0y0
2 )(

1 with each xkyk
xN

−−− · · · −−−
−

−−− · · · −−−

−−− · · · −−−

xN
−
1yN

1yN
1

x0y0

1yN

−−−

xN

∈

−

−

−

−

n

1

3

−−− · · · −−−
vk, where x0y0 =
x0y0 is

−−−

On the other hand, a Hamiltonian cycle in G, say

00, 00

, will lead similarly to 00 = x0y0

{
cycle if and only if xN yN = 00, which happens if and only if N is odd.

−−− · · · −−−

}

00, 00

vN =
= v0
xN yN . And it will yield an Eulerian

−−− · · · −−−

{

}

We conclude that if n mod 4 = 2, we should add the special edge u0

u1 to G.
Then its Hamiltonian cycles will correspond precisely to all of the centrally symmetric
n knight cycles; they’re Bergholtian if the special edge is used, Eulerian otherwise.
m

−−−

×

December 4, 2025

multigraph
de Jaenisch

7.2.2.4

ANSWERS TO EXERCISES

81

×
−−−

But if n mod 4 = 0, there aren’t any m

n Eulerian cycles. We get the Bergholtian
u1, where ‘!’ is a new vertex.

2

4

4

!

n

n

m

−
2

−−−

xy, xy

, and y(cid:2) =

−
2 +k, x(cid:2) =

−
2
x(cid:2)y(cid:2) and xy

, y =
we have both xy

ones by adding two special edges, u0
137. Again we construct G with N = mn/2 vertices
. But there’s a new
complication: G is a multigraph, with four edges that occur twice! Indeed, when x =
m
k < 4 and k(cid:2) = (k+2) mod 4,
is a double edge.
11
07
10
67 ,
70 ,
66 ,
37
’.) The
wx, yz
40 . (We write ‘
. . . ,
}
33
25
22
double edges for this case turn out to be
44 ; and
52
55
−−−
G also has 76 single edges. Algorithm H needs fewer than 800 megamems to visit each
of G’s 2,451,830 Hamiltonian cycles, one of which is
11
01
66
76

For example, G has 32 vertices when m = n = 8, namely
17
60 , . . . ,

wx
yz ’ as a convenient shorthand for vertex ‘
{
32
34
45 ,
43 ,

2 +k(cid:2), where 0
−
xy, xy

x(cid:2)y(cid:2), x(cid:2)y(cid:2)
00
77 ,

≤
} −−− {

}
01
76 , . . . ,

x(cid:2)y(cid:2). Hence

35
42 ,

−−−

−−−

−−−

−−−

−−−

14
63

06
71

27
50

31
46

10
67

02
75

23
54

33
44

12
65

37
40

32
45

03
74

22
55

16
61

23
54

24
53

21
56

00
77

35
42

30
47

26
51

07
70

15
62

36
41

20
57

13
64

34
43

24
53

05
72

17
60

25
52

04
73

{

}

{

4

00
77 .

This cycle doesn’t use any of the double edges; so we can uniquely extract a corre-
sponding knight path that begins at 00, proceeding from left to right:

00 21 42 30 51 70 62 41 20 01 13 34 53 72 60 52 73 61 40 32 11 03 22 14 06 27 46 67 75 54 33 12 00 .

Hmmm. Bad luck. Only 32 cells have been touched before the knight has returned to
its starting point, 00; hence this Hamiltonian cycle of G doesn’t correspond to a valid
knight’s cycle of the full 8

8 board. (Its complement tours the other 32 cells.)
Let’s try again. Here’s another Hamiltonian cycle that’s double-move free:
12
02
21
65
75
56

×
22
55

04
73

16
61

37
40

25
52

17
60

05
72

13
64

34
43

24
53

03
74

11
66

32
45

33
44

23
54

35
42

00
77

30
47

26
51

07
70

15
62

36
41

20
57

01
76

14
63

06
71

27
50

31
46

10
67

00
77 .

This one brings better news when we extract the corresponding knight path:

00 21 42 30 51 70 62 41 20 01 22 14 06 27 46 67 75 54 73 61 40 52 60 72 64 43 24 03 11 32 44 65 77 ;
aha, it ends in 77! We get a full knight’s cycle by appending the complementary steps.

Consider now a Hamiltonian cycle of G that does use one of the double edges:
00
32
21
77 .
45
56

11
66

03
74

24
53

34
43

22
55

14
63

06
71

27
50

31
46

10
67

02
75

23
54

33
44

12
65

35
42

30
47

26
51

07
70

15
62

36
41

01
76

13
64

05
72

25
52

04
73

16
61

37
40

00
77

(The culprit is ‘

34
43 ’.) Knight-path extraction is now ambiguous,

20
57
22
55 ’, aka ‘

17
60
22
55

−−−

34
43

−−−

05
72
3

00 21 42 30 51 70 62 41 20 01 13 05 17 25 04 16 37 45 66 74 53 34 ∗ 22 14 06 27 46 67 75 54 33 12 00 ,
because 34 can be followed by either 22 or 55. We’d better choose 55; that will
complement all of the subsequent steps, and we’ll end up with 77 as desired.

Next let’s look at the path in G that corresponds to a famous knight’s cycle that
C. F. de Jaenisch [Trait´e des applications de l’analyse math. au jeu des ´echecs 2 (1862),
35–37] proudly called “seven-fold reentrant”:
01
35
76
42

20
57

36
41

15
62

07
70

26
51

34
43

22
55

10
67

02
75

14
63

06
71

27
50

31
46

12
65

00
77

21
56

33
44

32
45

24
53

03
74

11
66

30
47

23
54

04
73

16
61

37
40

25
52

17
60

13
64

00
77 .

This one has three double edges, hence 2

= 8 ways to resolve its ambiguities:

00 21 33 45 ∗ 24 03 11 30 42 ∗ 23 04 16 37 25 17 05 13 01 20 41 62 70 51 43 ∗ 22 10 02 14 06 27 46 65 77 .

Four of those eight will produce 77 at the right.

Can all four of the double edges participate? Yes, but such cases are much rarer:
14
21
63
56

02
75

10
67

31
46

34
43

22
55

01
76

20
57

36
41

17
60

05
72

13
64

25
52

33
44

12
65

35
42

23
54

04
73

16
61

37
40

32
45

24
53

03
74

11
66

30
47

26
51

07
70

15
62

27
50

06
71

00
77 .

00
77

Eight of the sixteen knight-path extractions are therefore fruitful in
00 21 42 ∗ 23 04 16 37 45 ∗ 24 03 11 30 51 70 62 50 71 63 75 67 46 34 ∗ 22 01 20 41 60 72 64 52 ∗ 33 12 00 .
Altogether the Hamiltonian cycles of G include exactly 1076876 without double
edges, of which 536360 are unlucky; plus (978316, 341706, 52192, 2740) that have
respectively (1, 2, 3, 4) doubles. That makes 1076876
341706 +
2740 = 2432932 centrally symmetric tours, which form 608233 sets of 4.
4

536360 + 978316 + 2

52192 + 8

−

·

·

·

December 4, 2025

82

ANSWERS TO EXERCISES

7.2.2.4

138. (Each value of m is accompanied by the totals for n = 3, 5, 7, . . . .)

Vertical symmetry. m = 6: 0, 4, 530, 20582, 994660, 45129332, 2082753196.
m = 10: 4, 2266, 18480426, 56275825112. m = 14: 24, 722396, 539780910056. m = 18:
276, 238539296. m = 22: 2604. m = 26: 25736. m = 30: 248816.

Eulerian symmetry. m = 6: 0, 0, 526, 22210, 1477090, 100121632, 6606415888.
m = 10: 0, 1212, 16330492, 49470226538. m = 14: 16, 498926, 529843978930. m = 18:
124, 167812624. m = 22: 1404. m = 26: 12824. m = 30: 126696.

Bergholtian symmetry. m = 6: 0, 0, 38, 3724, 363594, 19156740, 1265006728.
m = 10: 4, 494, 3346312, 19308979910. m = 14: 8, 123028, 101557666784. m = 18:
152, 47966908. m = 22: 1200. m = 26: 12912. m = 30: 122120.

(We might as well also record here the other cases of Bergholtian symmetry.
m = 8: 0, 22, 21968, 17072474, 8868635684. m = 12: 0, 8858, 452675596. m = 16: 48,
3145086. m = 20: 352. m = 24: 3752. m = 28: 34768. m = 32: 346128.)

(Algorithm H’s running time for these graphs G is roughly 500 mems per solution.

The totals for (m, n) = (6, 15) and (14, 7) were obtained by Algorithm E.)

Vertical symmetry
Eulerian symmetry
Bergholtian symmetry
dynamic enumeration
self-loops
transpose
Marlow
census
central wedges
canonical bunches

139. Let G be a graph with 25 vertices, one for each class of four cells
that are rotationally equivalent, where ¯x = 9
and
we must omit the self-loops from
thermore, we remove one of the two edges between

}
x. Adjacency is deﬁned by giraﬀe moves;
to themselves. Fur-
.
and
}
This 51-edge graph has 56 Hamiltonian cycles (found in just 33 Kμ); but the
actual number is 100, because 44 of those cycles include the double edge. That yields
100 ways to cover a 10

10 board with symmetrical Hamiltonian cycles.

32, 26, 67, 73
{
22, 27, 77, 72
{

−
23, 37, 76, 62

xy, y¯x, ¯x¯y, ¯yx

33, 36, 66, 63

}
}

{

{

{

}

A cycle and its transpose are both counted. Hence there are exactly 50 essentially
[They were ﬁrst discovered by T. W. Marlow, shortly after he had
10 knight cycles with 90◦ symmetry.

distinct solutions.
enumerated the 415902 essentially distinct 10
See The Games and Puzzles Journal 2, 16 (15 May 1999), 288–291.]

×

×

141. Multiply the number of Hamiltonian cycles of the 8
by 64 (to place ‘1’) and by 2 (to place ‘2’): 1,698,222,644,548,096.

×

8 knight graph (

13 trillion)

≈

142. (a) If β is the wedge at 44 in C, then βτ is the wedge at 34 in the reﬂection. And
α4 = βρ. So βτ = α4ρρρτ = α4τ ρ = ¯α4. Continuing in this way we obtain ¯α4 ¯α3 ¯α2 ¯α1.

(b) ¯α2 ¯α1 ¯α4 ¯α3.

(c) ¯α3 ¯α2 ¯α1 ¯α4.

143. dDdD reﬂects to cCcC; the canonical bunch is CcCc, by (25).

144. False. In its equivalence class

abAB, bABa, ABab, BabA

, the smallest is ABab.

{

}

145. It would force a 4-cycle with two edges at the nearby corner.

146. αααα for α
∈ {
Eh, Fg, Gf, He, Ij, Ji, Kk, La, Ll, al, wx, yz

B, C, D, E, F, G, H, I, J, K, w, y

.

; αβαβ for αβ

}

∈ {

AL, Aa, Al, Bb, Cd, Dc,

148. For example, the ﬁxed point α1α2α3α4 = ¯α3 ¯α2 ¯α1 ¯α4 occurs if and only if α1 = ¯α3,
α2 = ¯α2, and α4 = ¯α4 (28
4 cases). Summing over all eight ﬁxed points yields the
4)/8. Similarly, without ‘a’,
answer (28
it’s (27

4
·
+ 28 + 28

4
3 + 27

4
·
3)/8.

+ 28
·
3

+ 28
3

+ 27 + 27

+ 27 + 27

+ 28 + 28

4 + 28

+ 27

·
2

·

2

2

4

2

2

4

2

+ 27
4

·

·

·

149. A census based on the 28
possible central wedges works well, as it did for knights.
(Notice that a giraﬀe’s wedge a subtends the angle θ(cid:2) = arctan
61.93◦, which is
signiﬁcantly wider than the angle 90◦
θ(cid:2) subtended by its wedge c.) As with knights, we
deal with 66771 canonical bunches; but this time we exclude code A instead of code a. It
turns out that 33975 of those canonical bunches — more than half! — have no solutions,
often because of subtle constraints that lead to nontrivial search trees. Of the remaining

15
8

−

≈

}

·
·

December 4, 2025

7.2.2.4

ANSWERS TO EXERCISES

83

32796 cases, bunch CdCd has the fewest solutions (110); bunch Baby has
a median number of solutions (847479); and bunch aaaa has the most
4.5 billion). (Bunch aaaa, which has multiplicity 8, also happens to
(
≈
be the graph G in Table 1 whose central wedges deﬁne a Cossack cross,
one of which is pictured here. Bunch CdCd has multiplicity 4.) The total
number of tours, taking multiplicities into account, is 1,018,865,516,976.

151. Now a bunch is deﬁned by a sequence of eight wedge codes α1β1α2β2α3β3α4β4,
where α1 and β1 are the wedges at 03 and 04; then α2 and β2 determine the wedges at
30 and 40 in a similar way, after we rotate the diagram 90◦ clockwise, etc. Therefore
α1β1α2β2α3β3α4β4, α2β2α3β3α4β4α1β1, α3β3α4β4α1β1α2β2, α4β4α1β1α2β2α3β3 are
.)
equivalent bunches. (The only codes that can appear in the top row are
For example, al-‘Adl¯ı’s closed tour (1) belongs to bunch EGABCAIG, which is
equivalent to ABCAIGEG, CAIGEGAB, and IGEGABCA, as well as to EGEIBCAB, EIBCABEG,
BCABEGEI, and ABEGEIBC after reﬂection. These bunches all have 83,205,370 solutions;
the census looks only at their canonical (lexicographically smallest) bunch, ABCAIGEG.
There are 210,771 canonical bunches altogether. But 29,984 of them have no solu-
tions, usually for obvious reasons. For example, α1β2 = AB forces a 4-cycle; α1β2α3β4 =
IIII forces a 6-cycle; α1β2α3β4 = CCCC forces a 12-cycle, for three choices of each of β1,
α2, β3, and α4. Canonical bunch CCCECECE has a unique solution; and so does CCCECCGE!
At the other extreme, EGEGEGEG has a whopping 3,046,049,272 solutions. The median
canonical bunch, AEEIECGC, has 859,162. (1,676,968,941,608 solutions are visited.)

A, B, C, E, G, I

{

}

Cossack cross
multiplicities
al-‘Adl¯ı
reﬂection
lexicographically smallest
canonical bunches
al-‘Adl¯ı
reﬂection
lexicographically smallest
transposition
reﬂection about a diagonal
Jelliss

(cid:4)→

(cid:4)→

152. Again we’ll have eight wedge codes α1β1α2β2α3β3α4β4 for the eight designated
wedges. We’ll base α1β1 on the wedges at 15 and 26; then α2β2 will deﬁne the wedges
at 21 and 12, after rotating the board 90◦ so that 21
26; and so on.
Bunch α1β1α2β2α3β3α4β4 will then be equivalent to bunch α2β2α3β3α4β4α1β1, as well
as to ¯β4 ¯α4 ¯β3 ¯α3 ¯β2 ¯α2 ¯β1 ¯α1 under reﬂection. The edges 15
26 are always present;
therefore the possible wedges at 15 are (D, F, i, K, w) and the possible wedges at 26 are
(c, g, J, k, x), in increasing order of their angles. Reﬂection takes D

15 and 12

g, etc.

c, F

−−−

−−−

(cid:4)→

(cid:4)→

07

For example, al-‘Adl¯ı’s closed tour (1) belongs to bunch KcFgFxiJ, which is
equivalent to FgFxiJKc, FxiJKcFg, and iJKcFgFx, as well as to iJwgFgDk, wgFgDkiJ,
FgDkiJwg, and DkiJwgFg after reﬂection. These bunches all have 11,550,362 solutions;
the census looks only at their canonical (lexicographically smallest) bunch, DkiJwgFg.
bunches, of which 49225 are canonical. However, it’s easy to see
that a bunch with αj βj = Kk forces a 4-cycle; we might as well omit all such cases.
That leaves us with 24

bunches, of which 41790 are canonical (see exercise 148).

There are 5

8

4

Among those 41790, bunch wxwxwxwx has the fewest solutions, with only 2112;
bunch iJiJiJiJ has the most, with 5,609,440,068; bunch DkFgFkig is a median, with
11,856,607. Altogether 1,692,674,826,245 solutions are visited.

154. The interconnecting steps of (9) are 2 . . 14, 16 . . 49, 51 . . 59, and 61 . . 64. Rotating
the diagram by 180◦ shows that this is type XII.

155. Only types I, II, III, X, and XI are unchanged by transposition (reﬂection about
, . . . ,
a diagonal). The other eight types must be split into two subtypes: IV and IV
XIII and XIII
, yielding 21 altogether. [The original 13-type classiﬁcation in Fig. 124
is due to G. P. Jelliss, The Games and Puzzles Journal 2, 16 (15 May 1999), 288.]

T

T

156. (357732461664, 166744766276, 483660455968, 498605611352, 333697459256,
812965778520,
1183196364192,
986042635376,
806039244560, 2491945752744, 2085173920272) for types (I, II,

1513974300904,

1547585659448,

. . . , XIII).

December 4, 2025

84

ANSWERS TO EXERCISES

7.2.2.4

(cid:9)I(cid:4)

(cid:9)Cp

(cid:9)(cid:128)(cid:5)

(cid:9)q(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)g(cid:11)

(cid:9)s(cid:26)

(cid:9)s(cid:8)

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)C(cid:4)

(cid:9)C(cid:11)

(cid:9)(cid:25)(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)Ir

(cid:9)J(cid:4)

(cid:9)g(cid:5)

(cid:9)q(cid:4)

(cid:9)C(cid:4)

(cid:9)gr

(cid:9)J(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I"

(cid:8)-"

(cid:3)u}

(cid:7)n#

(cid:3)(cid:137)"

(cid:9)v"

(cid:3)w(cid:26)

(cid:3)L(cid:8)

(cid:9)!"

(cid:3)J"

(cid:9)<"

(cid:9)w"

(cid:3)1"

(cid:3)1"

(cid:3)L(cid:26)

(cid:3)L(cid:8)

(cid:9)~"

(cid:0)-(cid:26)

(cid:3)L"

(cid:9)v(cid:5)

(cid:3)u"

(cid:9)!"

(cid:7)uM

(cid:3)Q(cid:8)

(cid:9)GF

(cid:3)a(cid:28)

(cid:9)n=

(cid:7)a(cid:29)

(cid:9)j=

(cid:3)(cid:136)=

(cid:9)(cid:136)(cid:26)

(cid:3)s(cid:8)

(cid:9)?>

(cid:8)A(cid:26)

(cid:3)(cid:25)=

(cid:9)S=

(cid:3)z=

(cid:9)E=

(cid:8)G(cid:26)

(cid:3)s(cid:8)

(cid:9)G"

(cid:3)](cid:29)

(cid:2)b=

(cid:3)G>

(cid:9)^=

(cid:8)_=

(cid:3)i(cid:26)

(cid:3)A(cid:8)

k-fold symmetry
Jelliss
magician

(cid:9)d(cid:4)

(cid:8)]#

(cid:9)(cid:137)(cid:5)

(cid:9)(cid:135)=

(cid:9)E#

(cid:8)~=

(cid:2)?(cid:20)

(cid:3)j(cid:8)

(cid:9)_=

(cid:3)z(cid:29)

(cid:3)A(cid:5)

(cid:3)(cid:128)(cid:26)

(cid:9)^=

(cid:9)kR

(cid:9)(cid:131)M

(cid:3);(cid:8)

(cid:9)d=

(cid:8)(cid:136)F

(cid:9)i>

(cid:9)6#

(cid:8)~(cid:4)

(cid:9)f(cid:29)

(cid:9)(cid:135)(cid:20)

(cid:3)(cid:130)(cid:8)

(a)

(cid:9)D"

(cid:9)(cid:134)"

(cid:9)Q>

(cid:9)6=

(cid:8)(cid:131)F

(cid:9)kR

(cid:9){(cid:26)

(cid:3)<(cid:8)

(b)

(cid:9)?=

(cid:9)z=

(cid:3)i>

(cid:3)C#

(cid:8)-#

(cid:9)v=

(cid:9)?(cid:26)

(cid:9)^(cid:8)

(c)

(cid:9)D"

(cid:3)(cid:134)(cid:4)

(cid:9)(cid:133)=

(cid:9)G"

(cid:9)]"

(cid:9)1F

(cid:9){(cid:26)

(cid:3)L(cid:8)

(cid:9)!>

(cid:7)(cid:128)#

(cid:3)(cid:138)(cid:4)

(cid:9)(cid:10)"

(cid:9)A(cid:4)

(cid:9)6(cid:29)

(cid:9)|(cid:26)

(cid:3)A(cid:8)

(cid:9)D=

(cid:7)(cid:136)=

(cid:9)(cid:131)=

(cid:3)S"

(cid:3)^(cid:26)

(cid:3)L>

(cid:9)J(cid:26)

(cid:3)s(cid:8)

(cid:9)?>

(cid:8)(cid:18)(cid:23)

(cid:8)(cid:25)"

(cid:9)I(cid:23)

(cid:0)L"

(cid:9)I(cid:29)

(cid:9)w(cid:26)

(cid:3)A(cid:8)

(cid:9)Z>

(cid:0)](cid:11)

(cid:8)j>

(cid:9)g"

(cid:8)~(cid:4)

(cid:9)6F

(cid:9)i[

(cid:3);(cid:8)

(cid:9)Z(cid:4)

(cid:0)f=

(cid:9)i=

(cid:3)(cid:131)=

(cid:3)E#

(cid:8)~=

(cid:2)iM

(cid:3)(cid:130)(cid:8)

(cid:9)Z2

Y]"

(cid:8)j>

(cid:9)6"

(cid:8)j>

(cid:9)(cid:133)R

(cid:8)(cid:131)M

(cid:3)Q(cid:8)

(cid:9)k"

(cid:9)m"

(cid:9)o=

(cid:9){"

(cid:9)m"

(cid:9)nR

(cid:9){.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)ǱF

(cid:9)c=

(cid:9)c=

(cid:9)kR

(cid:9)_F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)kF

(cid:9)z"

(cid:9)n=

(cid:9){"

(cid:9)Ǳ#

(cid:9)1F

(cid:9)a.

(cid:9)o(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:11)

(cid:9)(cid:25)(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)gr

(cid:9)q(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:11)

(cid:9)s(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)r

(cid:9)qr

(cid:9)|r

(cid:9)|(cid:4)

(cid:9)(cid:22)r

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I"

(cid:8)(cid:10)"

(cid:0)n"

(cid:3)n"

(cid:3)1"

(cid:9)1"

(cid:3)u(cid:26)

(cid:3)L(cid:8)

(cid:9)~"

(cid:0)Z"

(cid:9)n"

(cid:9)n#

(cid:3)n"

(cid:9)Z"

(cid:2)Q(cid:26)

(cid:3)L(cid:8)

(cid:9)!"

(cid:3)D"

(cid:9)n}

(cid:3)1}

(cid:3)!#

(cid:7)Z"

(cid:9)|(cid:26)

(cid:3)<(cid:8)

(cid:9)(cid:10)"

(cid:8)^"

(cid:3)o.

(cid:9)b(cid:26)

(cid:9)A=

(cid:9)E=

(cid:9)G(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)E"

(cid:9)]"

(cid:9);(cid:20)

(cid:9)Q#

(cid:9)Ǳ=

(cid:9)dF

(cid:9)i(cid:20)

(cid:3)Q(cid:8)

(cid:9)d>

(cid:8)^(cid:5)

(cid:3)q(cid:5)

(cid:9)(cid:134)}

(cid:9)m[

(cid:3)(cid:130)F

(cid:9)G$

(cid:3)o(cid:8)

(cid:9)I"

(cid:8)](cid:19)

(cid:9)bU

(cid:9)(cid:10)(cid:12)

(cid:8)s#

(cid:9)ZF

(cid:9)(cid:131)$

(cid:3)b(cid:8)

(cid:9)~"

(cid:9)Z"

(cid:9);(cid:20)

(cid:9);#

(cid:9)~#

(cid:9)ZR

(cid:9)(cid:131)(cid:20)

(cid:9)Q(cid:8)

(cid:9)!"

(cid:3)A>

(cid:9)o}

(cid:8)!r

P|(cid:20)

(cid:9)(cid:130)=

(cid:9)GM

(cid:3)(cid:130)(cid:8)

(g)

(cid:9)G"

(cid:3)A"

(cid:9)n=

(cid:9){"

(cid:3)-(cid:5)

(cid:9)wF

(cid:9)G.

(cid:9)o(cid:8)

(h)

(cid:9)~"

(cid:9)~"

(cid:9);(cid:20)

(cid:9)Q#

(cid:9)Z"

(cid:9)Z"

(cid:9);(cid:20)

(cid:9)Q(cid:8)

(i)

(cid:9)G(cid:5)

(cid:3)(cid:128)#

(cid:9)D(cid:28)

(cid:9)Ǳ>

(cid:3)j#

(cid:8)!>

(cid:9)|M

(cid:3)j(cid:8)

(cid:9)I(cid:11)

(cid:8)^(cid:26)

(cid:9)s=

(cid:9)(cid:136)(cid:11)

(cid:8)A>

(cid:9)s>

(cid:8)(cid:128)(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)D"

(cid:9)-"

(cid:9);(cid:20)

(cid:9);#

(cid:9)~"

(cid:9)Z"

(cid:9)u(cid:26)

(cid:9)L(cid:8)

(cid:9)?>

(cid:3)A(cid:28)

(cid:8)D(cid:5)

(cid:3)q#

(cid:9)m}

(cid:9)m>

(cid:3)J(cid:26)

(cid:3)^(cid:8)

(cid:9)k"

(cid:7)](cid:29)

(cid:2)Q=

(cid:8)kU

(cid:3)g#

(cid:8)Z>

(cid:2)jM

(cid:3)j(cid:8)

(cid:9)~#

(cid:0)~(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)"

(cid:9)(cid:22)"

(cid:9);M

(cid:3)Q(cid:8)

(cid:9)d#

(cid:8)Ǳ>

(cid:9)j>

(cid:8)j(cid:4)

(cid:8)gU

(cid:9)(cid:22)>

(cid:8)(cid:130)M

(cid:3)(cid:130)(cid:8)

(cid:9)_=

(cid:9)aR

(cid:9)k=

(cid:9){=

(cid:9)kR

(cid:9)kF

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)k"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)1F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)m#

(cid:9)n#

(cid:9)Ǳ#

(cid:9)ǱR

(cid:9)_F

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)I(cid:4)

(cid:9)Cr

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)Cr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:11)

(cid:9)s(cid:5)

(cid:9)|(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)Cr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:11)

(cid:9)(cid:25)(cid:26)

(cid:9)s(cid:8)

(cid:9)D"

(cid:3)D"

(cid:9)nM

(cid:3)Q"

(cid:9)D"

(cid:3)n"

(cid:9)L(cid:26)

(cid:3)L(cid:8)

(cid:9)D"

(cid:7)~"

(cid:2)Q>

(cid:9)L#

(cid:3)~"

(cid:2)D"

(cid:9)w(cid:26)

(cid:3)L(cid:8)

(cid:9)Z"

(cid:0)v"

(cid:9)n"

(cid:9)n"

(cid:9)1"

(cid:9)n"

(cid:3)Q(cid:26)

(cid:3)L(cid:8)

(cid:9)G(cid:28)

(cid:8)Ǳ(cid:5)

(cid:3)|(cid:5)

(cid:9)(cid:135)=

(cid:9)S2

(cid:3)g=

(cid:8)?(cid:26)

(cid:3)A(cid:8)

(cid:9)_=

(cid:7)a"

(cid:9)|=

(cid:3){=

(cid:9)z"

(cid:9)C=

P{M

(cid:3)(cid:130)(cid:8)

(cid:9)G"

(cid:8)^(cid:11)

(cid:9)Q(cid:26)

(cid:9)(cid:25)#

(cid:9)-=

(cid:9)i=

(cid:9)?(cid:26)

(cid:3)s(cid:8)

(cid:9)D(cid:11)

(cid:7)^>

(cid:9)j(cid:28)

(cid:3)D(cid:5)

(cid:3)(cid:128)=

(cid:9)aR

(cid:9)?M

(cid:3)Q(cid:8)

(cid:9)~(cid:4)

(cid:9)]=

(cid:9)d(cid:4)

(cid:8)(cid:18)2

(cid:9)I#

(cid:8)ZF

(cid:9)a.

(cid:9)o(cid:8)

(cid:9)_#

(cid:3)-U

(cid:9)(cid:10)#

(cid:8)~(cid:5)

:J#

(cid:9)~=

(cid:9)(cid:131)(cid:26)

(cid:3)(cid:25)(cid:8)

(m)

(cid:9)~(cid:12)

(cid:0)^(cid:5)

(cid:9)J=

(cid:9)z>

(cid:3)(cid:130)#

(cid:3)!=

(cid:9)?M

(cid:3)(cid:130)(cid:8)

(n)

(cid:9)(cid:10)"

(cid:9)J"

(cid:9);"

(cid:3)bF

(cid:9)c"

(cid:3)<"

(cid:9)u(cid:20)

(cid:9)Q(cid:8)

(o)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)GF

(cid:3)?"

(cid:3)1#

(cid:7)1R

(cid:9)(cid:131)T

(cid:3)b(cid:8)

(cid:9)G"

(cid:3)^(cid:28)

(cid:3)1=

(cid:3)(cid:136)(cid:5)

(cid:9)(cid:134)}

(cid:9)Ǳ>

(cid:3)|(cid:26)

(cid:3)A(cid:8)

(cid:9)D"

(cid:3)C=

(cid:0){(cid:5)

(cid:9)(cid:128)2

(cid:9)C#

(cid:8)Ǳ>

(cid:9)J(cid:26)

(cid:3)s(cid:8)

(cid:9)?(cid:5)

(cid:3)J>

(cid:9)J=

(cid:3)z#

(cid:3)Z(cid:4)

(cid:9)f=

(cid:9)G(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)E=

(cid:8)E2

(cid:9)(cid:22)(cid:19)

(cid:8)(cid:130)}

(cid:9)~(cid:4)

(cid:0)(cid:22)>

(cid:9)(cid:130)M

(cid:3)(cid:130)(cid:8)

(cid:9)E(cid:4)

(cid:8)f"

(cid:9)(cid:130)>

(cid:3)Q=

(cid:3)E"

(cid:9)~>

(cid:2)QM

(cid:3)(cid:130)(cid:8)

(cid:9)E>

(cid:8)]>

(cid:8)(cid:22)(cid:4)

(cid:8)](cid:4)

(cid:9)f"

(cid:9)Z"

(cid:9)QM

(cid:3)Q(cid:8)

(cid:9)_"

(cid:9)ǱF

(cid:9){"

(cid:9)1#

(cid:9)1"

(cid:9)ǱF

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)ǱF

(cid:9){=

(cid:9)c#

(cid:9)ǱR

(cid:9)_F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_F

(cid:9)z"

(cid:9)b"

(cid:9)b"

(cid:9)1"

(cid:9)1F

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:5)

(cid:9)(cid:128)(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:11)

(cid:9)sp

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)r

(cid:9)q(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)r

(cid:9)qr

(cid:9)qr

(cid:9)|(cid:4)

(cid:9)(cid:22)r

(cid:9)|(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I"

(cid:8)J"

(cid:3)Q(cid:28)

(cid:3)n"

(cid:3)-"

(cid:3)n>

(cid:9)w(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)Z"

(cid:0)-"

(cid:9)n"

(cid:9)1#

(cid:3)1"

(cid:9)-"

(cid:9)uM

(cid:3);(cid:8)

(cid:9)!"

(cid:3)!"

(cid:9)n}

(cid:3)1}

(cid:3)v#

(cid:7)!"

(cid:9)qM

(cid:3);(cid:8)

(cid:9)_R

(cid:7)a[

(cid:3)Q=

(cid:9)a=

(cid:3)a#

(cid:9)Z=

(cid:9)?[

(cid:3)j(cid:8)

(cid:9)?"

(cid:3)(cid:134)r

(cid:9)u(cid:4)

(cid:9)(cid:22)U

(cid:9)]#

(cid:8)(cid:137)=

(cid:9)S(cid:26)

(cid:3)^(cid:8)

(cid:9)?>

(cid:8)(cid:134)(cid:5)

(cid:3)q(cid:29)

(cid:9)(cid:134)#

(cid:3)Ǳ(cid:28)

(cid:9)m=

(cid:0)iM

(cid:3)(cid:130)(cid:8)

(cid:9)_(cid:4)

(cid:9)](cid:11)

(cid:9)(cid:130)=

(cid:9)(cid:131)(cid:4)

(cid:9)(cid:18)#

(cid:9)~F

(cid:9)i$

(cid:3)o(cid:8)

(cid:9)?}

(cid:8)->

(cid:3)(cid:22)#

(cid:8)vR

(cid:9)?"

(cid:9)6(cid:29)

(cid:2)w(cid:26)

(cid:3)A(cid:8)

(cid:9)!>

(cid:7)(cid:135)>

(cid:3)(cid:130)=

(cid:3)E#

(cid:8)~#

(cid:9)(cid:138)(cid:20)

(cid:9)(cid:130)(cid:26)

(cid:9)^(cid:8)

(s)

(cid:9)!#

(cid:9)-"

(cid:9)J(cid:29)

(cid:9)w#

(cid:8)v"

(cid:9)s"

(cid:9)w.

(cid:9)b(cid:8)

(t)

(cid:9)!(cid:26)

(cid:3)A(cid:29)

(cid:9)(cid:134)"

(cid:3)(cid:135)>

(cid:9)w=

(cid:8)iR

(cid:9)i(cid:26)

(cid:3)<(cid:8)

(u)

(cid:9)!>

(cid:7)A[

(cid:3)j#

(cid:9)Ǳ"

(cid:9)Ǳ"

(cid:9)6(cid:29)

(cid:9)w(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)(cid:10)(cid:29)

(cid:8)(cid:128)>

(cid:3)J=

(cid:3)kU

(cid:3)C(cid:5)

(cid:8)J>

(cid:9)(cid:128)(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)S}

(cid:3)v}

(cid:3)v(cid:4)

(cid:3)f=

(cid:9)?(cid:26)

(cid:3)^(cid:8)

(cid:9)D(cid:26)

(cid:3)Ap

(cid:9)(cid:135)p

(cid:9)|p

(cid:9)|#

(cid:9)(cid:138)R

(cid:9)G(cid:26)

(cid:3)<(cid:8)

(cid:9)dF

(cid:8)z>

(cid:3);=

(cid:3)z=

(cid:3)a"

(cid:8)Z>

YQ[

(cid:3)j(cid:8)

(cid:9)d2

(cid:8)fU

(cid:8)gU

(cid:8)](cid:4)

(cid:8)f(cid:4)

(cid:9)]R

(cid:9)iM

(cid:3)Q(cid:8)

(cid:9)d#

(cid:8)m(cid:28)

(cid:9)(cid:137)(cid:28)

(cid:0)(cid:138)>

(cid:0)g(cid:4)

(cid:8)g=

(cid:9)iM

(cid:3)j(cid:8)

(cid:9)kR

(cid:9)z.

(cid:9)o=

(cid:9)z=

(cid:9)_=

(cid:9)kR

(cid:9)z.

(cid:9)o(cid:8)

(cid:9)kF

(cid:9)zF

(cid:9)cF

(cid:9)c"

(cid:9)n"

(cid:9)1F

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)Ǳ#

(cid:9)n#

(cid:9)m#

(cid:9)m"

(cid:9)mF

(cid:9)c.

(cid:9)o(cid:8)

Fig. A–19. A gallery of

[These results are unexpected. Why does Type II occur less than half as often
as Type I? But the totals are otherwise roughly in line with the prediction that a type
with k-fold symmetry will occur about 1/k times as often as the unsymmetrical types
XII and XIII. (The respective values of k are (8, 8, 4, 4, 4, 2, 2, 2, 2, 2, 2, 1, 1).)]

157. (a) 431,873,707,240. (b) 0! (No explanation for this lack of solutions is known.)
(c) Although six full classes force 48 of the 64 edges, there actually are 6720

solutions. For example, Fig. A–19(c) has all the edges of classes A, C, E, F, G, S.

[G. P. Jelliss devised Fig. A–19(b), whose moves of slope +2 solve (a), in Chessics
2, 22 (Summer 1985), 66. He observed that a magician who memorizes a single solution
to (a) can perform the following trick: A spectator places a white knight and a black
knight anywhere on the board, a knight’s move apart; the magician then captures the
black knight with the white knight, the slow way, after ﬁrst visiting every other square.]

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:20)
(cid:13)
(cid:21)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:12)
$
%
3
’
(cid:14)
)

W
9
(cid:24)
Y
>
(cid:5)
7
&
(cid:6)
t
K
+
:
(cid:2)
(cid:7)
(cid:29)
(cid:11)
$
.
3
N
8
(cid:31)
4
*
5
P
M
%
&
N
O
(
*
\
Y
(cid:0)
#
(cid:29)
(cid:26)
&
3
(cid:13)
(
)

0
(cid:7)
(cid:3)
(cid:29)
(cid:5)
T
&
H
/
)

\
:
(cid:2)
(cid:7)
T
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
N
)
*
9
,
(cid:0)
(cid:7)
(cid:8)
.
8
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
$
l
N
(
(cid:15)
*
0
5
P
(cid:0)
(cid:20)
@
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
(cid:31)
4
5
(cid:7)
(cid:8)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
@
N
(cid:14)
(cid:15)
W
X
P
(cid:0)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
l
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
U
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
(cid:19)
%
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:29)
p
(cid:19)
%
&
(cid:30)
(cid:14)
(
4
(cid:16)
+
(cid:17)
:
%
@
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
‘
(cid:6)
(
)
(cid:15)
0
5
(cid:2)
(cid:7)
(cid:20)
.
O
8
)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:11)
.
8
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:19)
[
N
(cid:21)
W
(cid:24)
P
(cid:0)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
.
&
/
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
’
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
(cid:26)
$
&
(cid:6)
(cid:129)
(
(cid:31)
(cid:15)
*
0
5
P
[
N
O
*
P
(cid:0)
(cid:8)
(cid:5)
&
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
(cid:12)
@
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
.
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:5)
(cid:19)
(cid:20)
H
(cid:21)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
‘
N
(cid:14)
(
(cid:31)
(cid:15)
e
+
(cid:17)
,
(cid:19)
[
@
N
(cid:21)
(cid:15)
W
X
P
(cid:0)
U
(cid:20)
3
O
(cid:31)

(cid:2)
(cid:8)
(cid:3)
#
(cid:4)
(cid:19)
$
%
N
(cid:14)
)
W
9
(cid:24)
Y
(cid:0)
(cid:11)
(cid:19)
.
&
(cid:14)
t
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
K
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
T
N
O
8
*
9
,
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:26)
$
%
&
(cid:6)
(cid:129)
(
)
*
\
Y
(cid:7)
(cid:26)
.
(cid:13)
8
)
(cid:0)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
H
8
V

(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
$
7
3
N
8
)

*
9
Y
(cid:7)
#
(cid:29)
T
&
3
/
)

\
:
(cid:2)
(cid:7)
(cid:29)
(cid:26)
7
&
3
(cid:13)
t
)

+
:
(cid:7)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:26)
$
%
@
3
(cid:129)
(cid:31)
h
*
9
5
Y
(cid:7)
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
>
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
$
@
N
*
P
(cid:0)
(cid:7)
(cid:8)
U
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
p
(cid:19)
%
(cid:30)
(cid:14)
4
(cid:16)
9
(cid:17)
:
(cid:2)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
$
%
‘
3
N
(

*
+
,
(cid:7)
(cid:26)
%
@
3
(cid:13)

9
:
(cid:7)
(cid:8)
(cid:26)
%
(cid:6)
(cid:13)
9
:
(cid:7)
(cid:8)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
>
(cid:29)
(cid:11)
(cid:20)
&
3
O
(
V
4
0
5
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
@
3
4
5
(cid:2)
(cid:7)
(cid:8)
(cid:29)
(cid:20)
%
3
O

9
:
(cid:2)
(cid:8)
2
(cid:26)
%
3
(cid:13)
(cid:31)

9
:
(cid:7)
(cid:8)
(cid:23)
$
%
(cid:129)
(cid:14)
e
9
(cid:24)
,
(cid:0)
(cid:26)
&
(cid:13)
(
0
(cid:0)
(cid:7)
(cid:3)
(cid:5)
&
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
&
’
(
(cid:15)
*
0
5
P
(cid:0)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
3
(cid:13)

9
:
(cid:7)
(cid:8)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:29)
r
(cid:26)
H
(cid:13)
(cid:31)
h
5
(cid:7)
(cid:8)
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
l
N
(cid:14)
(
(cid:15)
W
\
X
Y
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:29)
(cid:20)
%
3
O

9
:
(cid:2)
(cid:8)
U
%
3

9
:
(cid:2)
(cid:7)
(cid:8)
U
(cid:11)
(cid:19)
%
3
(cid:14)
h
(cid:16)
9
(cid:17)
:
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
%
&
3
x
(
(cid:31)
4
(cid:16)
+
X
:
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:12)
$
%
&
’
(cid:14)
(
V
W
\
(cid:24)
Y
$
.
&
(cid:129)
/
*
0
P
(cid:0)
(cid:7)
}
(cid:29)
(cid:26)
3
(cid:13)
K

(cid:7)
(cid:8)
(cid:3)
$
7
&
(cid:6)
N
t
*
+
Y
(cid:7)
#
(cid:29)
(cid:5)
H
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
p
T
&
(cid:30)
/
V
4
\
5
:
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
%
@
3
)

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:19)
T
@
3
(cid:14)
8

(cid:16)
9
(cid:24)
:
(cid:5)
%
(cid:6)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:26)
@
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:11)
$
N
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
>
M
&
N
O
(
(cid:31)
*
0
P
(cid:0)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
(cid:129)
(cid:14)
(cid:15)
e
X
P
(cid:0)
(cid:20)
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
U
.
3
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
(cid:4)
(cid:19)
$
%
N
(cid:14)
W
9
(cid:24)
Y
(cid:0)
(cid:19)
‘
(cid:14)
(
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
r
(cid:19)
@
H
(cid:14)
h
(cid:16)
X
(cid:2)
(cid:8)
%
@
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:9)
(cid:7)
#
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
%
‘
(cid:6)
(
)
+
:
(cid:2)
(cid:7)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:4)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:19)
.
(cid:14)
8
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
>
.
&
t
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:26)
$
’
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
M
(cid:129)
x
e
(cid:24)
P
(cid:0)
>
(cid:4)
(cid:5)
(cid:6)
V
(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
.
(cid:129)
(cid:14)
8
e
(cid:24)
P
(cid:4)
(cid:5)
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
.
(cid:30)
(cid:14)
8

(cid:16)
(cid:24)
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
l
3
N
(cid:14)
(
4
W
\
X
(cid:19)
(cid:20)
%
@
(cid:21)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
U
(cid:11)
.
3
8
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:19)
M
%
@
N
x
)
e
9
(cid:24)
Y
(cid:0)
(cid:4)
(cid:11)
.
8
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:11)
(cid:19)
[
3
N
(cid:21)
V
4
W
X
P
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
p
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
(cid:5)
(cid:19)
$
(cid:6)
N
(cid:14)
V
W
(cid:24)
P
(cid:28)
(cid:19)
$
.
N
(cid:14)
8
V
e
(cid:24)
P
}
$
.
&
N
/
K
*
0
P
(cid:0)
(cid:7)
#
$
.
&
N
t
)
*
0
P
(cid:0)
(cid:7)
#
(cid:29)
.
&
3
t
)

0
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
7
&
(cid:30)
t
)

+
:
(cid:2)
(cid:7)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:12)
$
@
’
(cid:14)
K
W
(cid:24)
P
(cid:0)
$
.
@
N
8
)
*
P
(cid:0)
(cid:7)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
r
(cid:19)
H
(cid:14)
(cid:31)
h
(cid:16)
X
(cid:2)
(cid:8)
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
$
%
@
N
(cid:14)
)
e
9
(cid:24)
,
(cid:0)
.
@
(cid:14)
8
(cid:16)
(cid:24)
(cid:0)
(cid:2)
r
H
h
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
%
(cid:13)
x
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:4)
(cid:11)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
>
(cid:29)
(cid:19)
(cid:20)
&
3
(cid:21)
(
K

(cid:16)
0
(cid:24)
(cid:2)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
@
’
)
*
P
(cid:0)
(cid:7)
(cid:8)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
.
&
3
/
(cid:31)

0
(cid:2)
(cid:7)
(cid:3)
#
(cid:26)
$
%
(cid:129)
)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
.
&
(cid:6)
t
0
(cid:2)
(cid:7)
(cid:3)
(cid:5)
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
$
%
@
(cid:129)
(cid:14)
(cid:15)
e
9
X
,
(cid:0)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
3
(cid:13)

(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
@
(cid:13)
(cid:15)
9
5
:
(cid:0)
(cid:7)
(cid:26)
(cid:20)
(cid:13)
O
(cid:31)
(cid:0)
(cid:8)
(cid:3)
p
(cid:26)
$
(cid:6)
(cid:129)
(cid:31)
(cid:15)
*
5
P
(cid:7)
[
(cid:129)
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
(cid:11)
$
%
‘
3
N
(
)
h
*
+
5
,
(cid:19)
(cid:20)
T
3
x
8

(cid:16)
9
(cid:24)
:
#
(cid:29)
(cid:11)
%
3
h
9
5
:
(cid:2)
(cid:7)
(cid:20)
%
&
3
O
(

\
:
(cid:2)
U
(cid:11)
(cid:19)
%
3
(cid:14)
h
(cid:16)
9
(cid:17)
:
(cid:2)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
%
‘
3
x
(
(cid:31)
4
(cid:16)
+
X
:
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:19)
$
%
&
N
(cid:14)
(
)
W
\
(cid:24)
Y
#
(cid:19)
.
&
(cid:14)
t
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
#
2
(cid:11)
&
3
(
)
4
0
5
(cid:2)
(cid:7)
(cid:29)
(cid:19)
(cid:20)
7
&
3
(cid:21)
t
)

(cid:16)
+
(cid:24)
:
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
@
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
.
x
8
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
&
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
7
O
8
9
:
(cid:0)
(cid:2)
(cid:9)
(cid:7)
#
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
.
&
x
t
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
&
x
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
#
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
.
&
x
t
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
.
&
x
t
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:26)
&
(cid:13)
(
)
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:11)
(cid:20)
.
&
O
t
)
(cid:15)
0
5
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:19)
&
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
(cid:5)
(cid:19)
.
&
(cid:6)
(cid:14)
t
)
(cid:16)
0
(cid:24)
(cid:2)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
&
N
(cid:14)
(
(cid:15)
W
\
X
Y
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
(cid:20)
x
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
.
3
x
8
V
4
(cid:16)
X
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
$
%
&
(cid:6)
N
(
)
*
\
Y
(cid:7)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
(cid:31)
*
0
P
(cid:0)
(cid:7)
(cid:5)
$
&
(cid:6)
N
(
(cid:31)
*
0
P
(cid:7)
(cid:4)
(cid:11)
$
&
N
(
(cid:15)
*
0
5
P
(cid:0)
>
(cid:29)
(cid:5)
(cid:19)
(cid:20)
&
H
(cid:21)
(
V

(cid:16)
0
(cid:24)
(cid:2)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
@
(cid:129)
(cid:14)
(cid:31)
(cid:15)
e
X
P
(cid:0)
[
(cid:6)
N
O
*
P
(cid:8)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
@
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
‘
N
O
(
*
0
P
(cid:0)
>
(cid:29)
(cid:5)
(cid:30)
K

(cid:2)
(cid:7)
(cid:8)
(cid:3)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
#
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
‘
(cid:13)
(
)
+
:
(cid:0)
(cid:7)
.
@
8
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
p
$
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
[
&
(cid:6)
N
O
(
(cid:15)
*
0
5
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
r
(cid:6)
(cid:31)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:6)
(cid:129)
*
9
Y
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
‘
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
M
l
N
O
(
(cid:31)
*
0
P
(cid:0)
r
$
(cid:6)
N
(cid:15)
*
5
P
(cid:7)
r
(cid:20)
&
(cid:6)
O
(
(cid:31)
(cid:15)
0
5
(cid:2)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
(cid:129)
(cid:31)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
r
$
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
M
&
(cid:6)
N
O
(
*
0
P
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
(cid:31)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
(cid:26)
$
&
(cid:6)
’
(
(cid:31)
*
0
P
(cid:7)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:20)
l
O
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
M
@
N
O
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:11)
M
N
O
(cid:15)
*
5
P
(cid:0)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
%
@
3
x
(cid:31)
4
(cid:16)
9
X
:
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
$
%
&
(cid:6)
N
(
)
*
\
Y
(cid:7)
(cid:28)
(cid:11)
.
&
t
V
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
.
&
N
O
/
*
0
P
(cid:0)
#
(cid:29)
(cid:5)
H
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
T
&
/
)
\
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:26)
.
&
3
(cid:13)
t
V

0
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
@
N
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
M
&
(cid:6)
N
O
(
*
0
P
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
(cid:26)
(cid:13)
(cid:31)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
[
3
N
O

*
P
(cid:8)
(cid:29)
(cid:5)
(cid:19)
%
(cid:30)
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
‘
’
(
(cid:15)
*
0
5
P
(cid:0)
(cid:20)
@
O
(cid:31)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
$
(cid:30)
N
(cid:31)

*
P
(cid:7)
(cid:8)
(cid:26)
$
%
&
(cid:6)
’
(
*
+
,
(cid:7)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
p
(cid:30)
V
4
5
(cid:2)
(cid:7)
(cid:8)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
’
(cid:14)
(
W
\
(cid:24)
Y
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
@
3
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
[
%
@
N
O
(cid:31)
*
9
,
(cid:0)
(cid:8)
(cid:5)
$
(cid:6)
N
*
P
(cid:7)
(cid:8)
>
r
&
(cid:6)
(
(cid:31)
(cid:15)
0
5
(cid:2)
(cid:7)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
T
8
(cid:31)
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:26)
$
&
(cid:129)
(
*
0
P
(cid:0)
(cid:7)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
@
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:5)
[
&
(cid:6)
N
O
(
(cid:31)
*
0
P
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
%
@
(cid:21)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:4)
(cid:11)
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
[
&
N
(cid:21)
(
(cid:15)
W
0
X
P
(cid:29)
(cid:11)
(cid:19)
(cid:20)
@
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
2
(cid:11)
$
%
&
3
N
(
)
4
*
\
5
Y
(cid:19)
(cid:20)
7
&
(cid:21)
t
)
(cid:16)
+
(cid:24)
:
(cid:0)
(cid:29)
(cid:26)
.
3
(cid:13)
8
(cid:31)

(cid:7)
(cid:3)
2
$
%
3
N

*
9
Y
(cid:7)
(cid:8)
#
(cid:5)
(cid:19)
%
&
(cid:6)
(cid:14)
(
)
(cid:16)
\
(cid:24)
:
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:28)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
l
N
(
(cid:15)
*
0
5
P
(cid:0)
(cid:29)
(cid:5)
(cid:20)
H
O
)

(cid:2)
(cid:8)
(cid:3)
T
8
9
:
(cid:0)
(cid:2)
(cid:7)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
(cid:26)
(cid:13)
K
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
(cid:31)
4
W
X
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
#
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
l
(cid:14)
(
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
>
(cid:4)
(cid:19)
(cid:14)
(cid:31)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
$
(cid:129)
(cid:14)
e
(cid:24)
P
(cid:0)
(cid:5)
(cid:19)
H
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:4)
(cid:19)
%
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:19)
‘
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:23)
(cid:6)
(cid:13)
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:8)
(cid:29)
(cid:20)
.
3
O
8
)

(cid:2)
(cid:3)
T
@
8
)
9
:
(cid:0)
(cid:2)
(cid:7)
>
.
8
K
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:26)
$
.
(cid:129)
8
)
*
P
(cid:0)
(cid:7)
p
.
(cid:6)
8
)
(cid:15)
5
(cid:2)
(cid:7)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
(cid:26)
$
%
&
(cid:129)
(
V
*
\
Y
(cid:0)
(cid:7)
(cid:19)
$
.
N
(cid:14)
8
e
(cid:24)
P
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
3
(cid:13)

(cid:7)
(cid:8)
(cid:3)
(cid:19)
%
@
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
p
(cid:26)
&
(cid:6)
(cid:13)
(
(cid:31)
(cid:15)
0
5
(cid:7)
[
(cid:129)
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
@
3
x
)
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:29)
(cid:20)
T
3
O
8
(cid:31)

9
:
(cid:2)
(cid:4)
$
%
N
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
U
(cid:11)
(cid:19)
3
(cid:14)
)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
T
&
3
x
/
(cid:31)
4
(cid:16)
\
X
:
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
&
’
(cid:14)
(
)
W
\
(cid:24)
Y
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
(cid:11)
.
&
3
t
)
h
0
5
(cid:2)
(cid:7)
(cid:29)
(cid:20)
7
&
3
O
t
)

+
:
(cid:2)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
%
@
(cid:13)
)
(cid:15)
9
5
:
(cid:0)
(cid:7)
(cid:20)
.
O
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:20)
&
O
(
0
(cid:0)
(cid:2)
(cid:3)
(cid:29)
p
(cid:30)
4
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
&
’
(
*
+
,
(cid:0)
(cid:7)
(cid:5)
&
(cid:30)
(

0
(cid:2)
(cid:7)
(cid:3)
U
(cid:19)
%
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:23)
%
&
(cid:6)
(cid:13)
(cid:14)
(
(cid:16)
+
(cid:24)
(cid:4)
(cid:11)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
&
3
(cid:21)
(
(cid:31)
h
(cid:16)
0
(cid:17)
(cid:2)
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
$
(cid:30)
N
)

*
P
(cid:7)
(cid:8)
}
7
8
K
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:11)
$
.
&
N
t
(cid:15)
*
0
5
P
(cid:0)
(cid:29)
(cid:20)
&
3
O
(
)

0
(cid:2)
(cid:3)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:6)
(cid:129)
*
9
Y
(cid:7)
(cid:8)
(cid:5)
(cid:26)
(cid:6)
(cid:13)
(cid:31)
(cid:7)
(cid:8)
(cid:3)
>
$
@
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:4)
$
N
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:19)
‘
(cid:14)
(
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
(cid:31)
4
W
9
X
Y
(cid:4)
(cid:19)
[
%
N
(cid:21)
(cid:31)
W
9
(cid:24)
,
(cid:0)
(cid:19)
$
@
N
(cid:14)
W
(cid:24)
P
(cid:0)
(cid:19)
@
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
#
(cid:4)
(cid:11)
(cid:19)
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
.
&
3
x
t
V
4
(cid:16)
0
X
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:23)
(cid:20)
(cid:13)
(cid:21)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
p
(cid:12)
$
%
(cid:30)
’
(cid:14)
)
4
W
9
(cid:17)
Y
>
(cid:20)
T
O
8
V
9
:
(cid:0)
(cid:2)
(cid:29)
$
.
3
N
8
(cid:31)

*
P
(cid:7)
#
(cid:29)
(cid:26)
$
%
&
3
’
(
)

*
+
,
(cid:7)
#
T
&
/
)
\
:
(cid:0)
(cid:2)
(cid:7)
(cid:29)
p
.
&
(cid:30)
t
(cid:31)
4
0
5
(cid:2)
(cid:7)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
$
%
l
N
(
V
(cid:15)
*
\
5
Y
(cid:0)
.
N
O
8
*
P
(cid:0)
(cid:29)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
@
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
r
(cid:19)
&
H
(cid:14)
(
(cid:31)
h
(cid:16)
0
X
(cid:2)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
l
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:19)
(cid:20)
@
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
>
(cid:19)
(cid:20)
&
(cid:21)
(
K
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
&
(cid:13)
(
0
(cid:0)
(cid:7)
(cid:3)
(cid:5)
(cid:26)
&
(cid:6)
(cid:13)
(
)
0
(cid:7)
(cid:3)
(cid:5)
.
(cid:30)
8

(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:26)
%
(cid:13)
(cid:15)
9
5
:
(cid:0)
(cid:7)
(cid:26)
(cid:20)
&
(cid:13)
O
(
)
0
(cid:0)
(cid:3)
(cid:5)
.
(cid:6)
8
)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:12)
$
%
H
’
(cid:14)

W
9
(cid:24)
Y
(cid:5)
(cid:26)
%
(cid:6)
(cid:13)
(cid:31)
9
:
(cid:7)
(cid:8)
}
(cid:29)
$
3
N
(cid:31)

*
P
(cid:7)
(cid:8)
(cid:26)
$
%
&
3
(cid:129)
(

*
\
Y
(cid:7)
(cid:23)
%
(cid:6)
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
r
(cid:26)
(cid:6)
(cid:13)
(cid:31)
(cid:15)
5
(cid:7)
(cid:8)
M
’
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
K
h
e
9
(cid:17)
,
[
T
N
O
8
(cid:31)
*
9
,
(cid:0)
(cid:29)
$
@
3
N

*
P
(cid:7)
(cid:8)
(cid:29)
%
@
3

9
:
(cid:2)
(cid:7)
(cid:8)
}
U
(cid:11)
%
3
K
h
9
5
:
(cid:2)
(cid:7)
(cid:29)
(cid:11)
(cid:19)
M
7
&
3
N
x
t
(cid:31)
h
e
+
(cid:17)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
&
’
(cid:14)
(
)
W
\
(cid:24)
Y
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
#
(cid:26)
&
(cid:13)
(
)
0
(cid:0)
(cid:7)
(cid:3)
>
(cid:29)
p
.
&
(cid:30)
t
V
4
0
5
(cid:2)
(cid:7)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
%
@
(cid:6)
)
9
:
(cid:2)
(cid:7)
(cid:8)
.
(cid:6)
8
(cid:15)
5
(cid:2)
(cid:7)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
@
3
(cid:14)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
%
x
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:26)
&
(cid:13)
(
(cid:31)
0
(cid:0)
(cid:7)
(cid:3)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
’
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
(cid:4)
[
&
N
O
(
(cid:31)
*
0
P
(cid:0)
(cid:12)
$
’
(cid:14)
W
(cid:24)
P
(cid:0)
(cid:5)
&
(cid:6)
(
)
0
(cid:2)
(cid:7)
(cid:3)
2
.
3
8
)

(cid:2)
(cid:7)
(cid:3)
(cid:5)
(cid:19)
7
(cid:30)
(cid:14)
8

(cid:16)
9
(cid:24)
:
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
(cid:129)
(
*
\
Y
(cid:0)
(cid:7)
(cid:5)
@
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
%
@
(cid:6)
)
9
:
(cid:2)
(cid:7)
(cid:8)
r
.
(cid:6)
8
(cid:31)
(cid:15)
5
(cid:2)
(cid:7)
(cid:11)
M
N
O
(cid:15)
*
5
P
(cid:0)
>
(cid:29)
(cid:20)
3
O
V

(cid:2)
(cid:8)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
&
’
(
(cid:31)
*
0
P
(cid:0)
(cid:7)
$
‘
N
(
*
0
P
(cid:0)
(cid:7)
(cid:29)
(cid:5)
(cid:19)
(cid:30)
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
4
W
9
X
Y
(cid:19)
(cid:20)
%
3
(cid:21)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:11)
(cid:19)
@
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
V
4
(cid:16)
X
(cid:2)
(cid:8)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
$
%
&
(cid:6)
N
(
)
*
\
Y
(cid:7)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
(cid:31)
*
0
P
(cid:0)
(cid:7)
(cid:26)
$
&
’
(
(cid:31)
*
0
P
(cid:0)
(cid:7)
p
$
&
(cid:6)
N
(
(cid:15)
*
0
5
P
>
(cid:29)
p
(cid:20)
&
(cid:30)
O
(
V
4
0
5
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
$
@
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
[
(cid:6)
N
O
*
P
(cid:8)
(cid:5)
@
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
@
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:11)
‘
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:11)
M
&
N
O
(
(cid:31)
(cid:15)
*
0
5
P
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
$
‘
(cid:6)
N
(
(cid:31)
(cid:15)
*
0
5
P
[
@
N
O
(cid:31)
*
P
(cid:0)
(cid:8)
>
(cid:4)
$
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
$
N
(cid:14)
(cid:15)
e
(cid:17)
P
(cid:0)
(cid:11)
(cid:19)
(cid:20)
&
(cid:21)
(
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
‘
O
(
0
(cid:0)
(cid:2)
(cid:3)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
‘
’
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:4)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
p
(cid:19)
.
(cid:30)
(cid:14)
8
4
(cid:16)
(cid:17)
(cid:2)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
(cid:129)
(
*
\
Y
(cid:0)
(cid:7)
@
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
&
H
(
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:20)
&
O
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
M
&
N
O
(
(cid:31)
(cid:15)
*
0
5
P
(cid:4)
(cid:11)
M
&
N
O
(
(cid:31)
(cid:15)
*
0
5
P
(cid:11)
(cid:19)
[
N
(cid:21)
(cid:15)
W
X
P
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
7.2.2.4

ANSWERS TO EXERCISES

85

(cid:9)I(cid:4)

(cid:9)C(cid:5)

(cid:9)(cid:128)(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:11)

(cid:9)sp

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)r

(cid:9)q(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)Cr

(cid:9)|(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:22)p

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)I"

(cid:8)J"

(cid:3)Q(cid:28)

(cid:3)n"

(cid:3)~"

(cid:2)n>

(cid:9)w(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)!"

(cid:3)-"

(cid:9)n(cid:4)

(cid:7)6"

(cid:9)(cid:137)"

(cid:3)1"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)!"

(cid:7)v"

(cid:3)Q"

(cid:9)1"

(cid:3)1"

(cid:9)n"

(cid:9)Q[

(cid:3);(cid:8)

(cid:9)_R

(cid:7)a[

(cid:3)Q=

(cid:9)a=

(cid:9)a"

(cid:9)Z=

(cid:9){[

(cid:3)(cid:130)(cid:8)

(cid:9)d(cid:11)

(cid:8)^#

(cid:9)(cid:137)(cid:5)

(cid:9)(cid:134)R

(cid:9)S(cid:5)

(cid:9)w=

(cid:9)GM

(cid:3)(cid:130)(cid:8)

(cid:9)!(cid:11)

(cid:7)^(cid:11)

(cid:9)(cid:130)=

(cid:9)i#

(cid:9)(cid:138)#

(cid:9)(cid:137)=

(cid:9)(cid:131)(cid:20)

(cid:9)j(cid:8)

(cid:9)_(cid:4)

(cid:9)](cid:19)

(cid:9)(cid:130)(cid:4)

(cid:9)I(cid:23)

(cid:9)(cid:25)#

(cid:9)ZR

(cid:9)i.

(cid:9)o(cid:8)

(cid:9)k"

(cid:3)(cid:135)(cid:11)

(cid:9)L>

(cid:9)(cid:22)(cid:23)

(cid:8)(cid:25)(cid:28)

(cid:9)-=

(cid:3)(cid:136)(cid:26)

(cid:3)A(cid:8)

(cid:9)_#

(cid:7)m#

(cid:9)(cid:138)#

(cid:9)(cid:137)#

(cid:9)(cid:138)#

(cid:9)(cid:137)p

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(d)

(cid:9)!(cid:4)

(cid:9)C"

(cid:9)!>

(cid:9)w"

(cid:3)v(cid:11)

(cid:9)L"

(cid:9)q(cid:26)

(cid:9)L(cid:8)

(e)

(cid:9)G(cid:28)

(cid:9)-#

(cid:3)(cid:138)=

(cid:9)S"

(cid:3)(cid:134)2

(cid:3)6(cid:29)

(cid:8)(cid:134)(cid:26)

(cid:3)^(cid:8)

(f)

(cid:9)_#

(cid:9)m#

(cid:9)(cid:138)#

(cid:9)(cid:137)#

(cid:9)(cid:138)#

(cid:9)(cid:137)>

(cid:9)q(cid:26)

(cid:3)s(cid:8)

(cid:9)I(cid:5)

(cid:8)J"

(cid:9)(cid:128)=

(cid:3)c#

(cid:3)Ǳ(cid:5)

(cid:3)J>

(cid:9)(cid:128)(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)!=

(cid:3)(cid:136)U

(cid:9)f=

(cid:8)S=

(cid:9)(cid:136)=

(cid:3)(cid:136)R

(cid:9)?(cid:26)

(cid:3)<(cid:8)

(cid:9)!#

(cid:9)v#

(cid:9)(cid:138)#

(cid:9)(cid:137)#

(cid:9)-#

(cid:9)D=

(cid:9)?[

(cid:3)j(cid:8)

(cid:9)E"

(cid:8)f>

(cid:0)Q=

(cid:3)z=

(cid:9)a}

(cid:8)Z=

Y(cid:131)[

(cid:3)j(cid:8)

(cid:9)d(cid:4)

(cid:8)]=

(cid:9)i"

(cid:3)g2

(cid:2)(cid:133)(cid:4)

(cid:8)]=

(cid:9)iM

(cid:3)j(cid:8)

(cid:9)Z#

(cid:0)~(cid:4)

(cid:9)(cid:22)U

(cid:9)g(cid:4)

(cid:8)g}

(cid:9)~=

(cid:0)(cid:131)[

(cid:3)j(cid:8)

(cid:9)_R

(cid:9)a"

(cid:9)b.

(cid:9)o=

(cid:9)_=

(cid:9)kR

(cid:9)z.

(cid:9)o(cid:8)

(cid:9)k"

(cid:9)mF

(cid:9)c=

(cid:9){R

(cid:9)k"

(cid:9)nF

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)m"

(cid:9)nR

(cid:9){"

(cid:9)1"

(cid:9)n"

(cid:9)o.

(cid:9)b(cid:8)

(cid:9)I(cid:4)

(cid:9)Cr

(cid:9)q(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)Cr

(cid:9)(cid:128)(cid:26)

(cid:9)s(cid:8)

(cid:9)Ir

(cid:9)J(cid:4)

(cid:9)gr

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)J(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)r

(cid:9)|(cid:11)

(cid:9)(cid:25)(cid:4)

(cid:9)g(cid:4)

(cid:9)Cr

(cid:9)|(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)Z"

(cid:0)v"

(cid:9)n(cid:11)

(cid:7)L"

(cid:9)s"

(cid:3)n"

(cid:3)u(cid:26)

(cid:3)L(cid:8)

(cid:9)~"

(cid:0)v#

(cid:3)n"

(cid:9)v(cid:5)

(cid:3)u"

(cid:9)~"

(cid:2)uM

(cid:3)Q(cid:8)

(cid:9)D"

(cid:3)-"

(cid:9)n(cid:4)

(cid:3)6#

(cid:9)D"

(cid:3)-"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)G"

(cid:3)^#

(cid:9)n(cid:29)

(cid:3)^=

(cid:3)G=

(cid:9)(cid:136)=

(cid:9)?(cid:26)

(cid:3)^(cid:8)

(cid:9)G"

(cid:3)](cid:29)

(cid:9)b(cid:5)

(cid:3)|>

(cid:9)f=

(cid:8)_R

(cid:9)(cid:131)$

(cid:3)b(cid:8)

(cid:9)d(cid:4)

(cid:8)]=

(cid:9)S(cid:5)

(cid:9)(cid:135)R

(cid:9)S(cid:4)

(cid:3)6=

(cid:9)G(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:4)

(cid:3)(cid:18)=

(cid:9)?=

(cid:3)?>

(cid:9)J(cid:4)

(cid:3)(cid:22)=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)E#

(cid:8)vF

(cid:9)i>

(cid:9)w#

(cid:3)Z"

(cid:9)fp

(cid:9)u(cid:20)

(cid:9)(cid:130)(cid:8)

(cid:9)d"

(cid:9)^"

(cid:3)L>

(cid:9)6=

(cid:8)(cid:136)(cid:5)

(cid:9)(cid:134)F

(cid:9)(cid:136)$

(cid:3)b(cid:8)

(j)

(cid:9)E(cid:12)

(cid:8)^R

(cid:9)S(cid:28)

(cid:7)1=

(cid:3)(cid:131)(cid:5)

(cid:3)(cid:134)F

(cid:9)G$

(cid:3)b(cid:8)

(k)

(cid:9)D"

(cid:3)]r

(cid:9)w>

(cid:9)(cid:22)(cid:4)

(cid:8)f"

(cid:9)-"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(l)

(cid:9)IF

(cid:8)S(cid:5)

(cid:3)u=

(cid:9)S"

(cid:3)(cid:135)>

(cid:9)6=

(cid:8)?(cid:26)

(cid:9)^(cid:8)

(cid:9)?"

(cid:3)^#

(cid:3)1=

(cid:9)z(cid:4)

(cid:9)f>

(cid:9)A=

(cid:3)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G#

(cid:8)-"

(cid:9)s(cid:5)

(cid:3)w"

(cid:9)]"

(cid:2)w>

(cid:9)u(cid:26)

(cid:3)A(cid:8)

(cid:9)GF

(cid:3)(cid:136)>

(cid:9)(cid:133)=

(cid:8)(cid:136)>

(cid:9)(cid:128)=

(cid:3)(cid:136)"

(cid:9)(cid:134)(cid:26)

(cid:3)<(cid:8)

(cid:9)E=

(cid:8)E(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g2

(cid:9)(cid:22)"

(cid:8)(cid:22)>

(cid:9)oM

(cid:3)j(cid:8)

(cid:9)~2

Y](cid:4)

(cid:8)g>

(cid:9)]=

(cid:8)(cid:131)"

(cid:9)(cid:22)=

P{M

(cid:3)(cid:130)(cid:8)

(cid:9)E(cid:4)

(cid:8)]=

(cid:9)i"

(cid:3)(cid:130)>

(cid:3)(cid:133)(cid:4)

(cid:8)f=

(cid:9)iM

(cid:3)(cid:130)(cid:8)

(cid:9)_"

(cid:9)m"

(cid:9)1"

(cid:9)1F

(cid:9){"

(cid:9)nF

(cid:9){.

(cid:9)b(cid:8)

(cid:9)kF

(cid:9)a"

(cid:9)1"

(cid:9)1"

(cid:9)o#

(cid:9)1F

(cid:9)a.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)ǱF

(cid:9){=

(cid:9){=

(cid:9)k"

(cid:9)ǱF

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:22)(cid:11)

(cid:9)s(cid:11)

(cid:9)s(cid:11)

(cid:9)s(cid:11)

(cid:9)(cid:25)(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:11)

(cid:9)s(cid:5)

(cid:9)|(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:10)r

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)Ir

(cid:9)J(cid:11)

(cid:9)s(cid:11)

(cid:9)(cid:25)(cid:11)

(cid:9)s(cid:4)

(cid:9)gr

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)!"

(cid:3)v"

(cid:3)n"

(cid:3)n#

(cid:3)1#

(cid:3)~(cid:29)

:J(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)D"

(cid:3)v"

(cid:3)u>

(cid:9)(cid:133)#

(cid:8)(cid:138)"

(cid:9)-"

(cid:3)w(cid:26)

(cid:3)<(cid:8)

(cid:9)D"

(cid:3)!#

(cid:3)n#

(cid:3)v#

(cid:7)-#

(cid:9)(cid:137)"

(cid:9)q(cid:26)

(cid:3)L(cid:8)

(cid:9)(cid:10)(cid:12)

(cid:8)^=

(cid:9)a=

(cid:9)?=

(cid:9)(cid:136)=

(cid:9)_F

(cid:3)?(cid:26)

(cid:3)<(cid:8)

(cid:9)E=

(cid:8)a(cid:28)

(cid:9)(cid:138)=

(cid:3)(cid:136)"

(cid:9)f(cid:4)

(cid:2)(cid:133)=

(cid:9)zM

(cid:3)j(cid:8)

(cid:9)G=

(cid:3)a=

(cid:3)z=

(cid:3)k#

(cid:3)-(cid:4)

(cid:9)C=

(cid:9)?M

(cid:3)j(cid:8)

(cid:9)G"

(cid:3)A(cid:4)

(cid:9)6>

(cid:9)I(cid:11)

(cid:8)s=

(cid:9)i=

(cid:9)G(cid:26)

(cid:3)A(cid:8)

(cid:9)_"

(cid:9)]2

(cid:9)6(cid:4)

(cid:8)f=

(cid:9)d"

(cid:9)vF

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)I(cid:4)

(cid:8)]=

(cid:9)z=

(cid:9)(cid:131)2

(cid:3)C#

(cid:8)~R

(cid:9)?$

(cid:3)o(cid:8)

(p)

(cid:9)G(cid:11)

(cid:8)A#

(cid:9)(cid:137)R

(cid:9)k"

(cid:3)b(cid:4)

(cid:9)(cid:133)=

(cid:9)G(cid:26)

(cid:3)A(cid:8)

(q)

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:18)R

(cid:9)(cid:131)"

(cid:9)<"

(cid:9)w"

(cid:3)(cid:133)r

(cid:9)u(cid:26)

(cid:9)s(cid:8)

(r)

(cid:9)(cid:10)"

(cid:8)Ǳ"

(cid:9)Q=

(cid:9){=

(cid:3)S"

(cid:9)(cid:128)"

(cid:9)u$

(cid:3)b(cid:8)

(cid:9)k(cid:11)

(cid:7)^(cid:26)

(cid:9)s=

(cid:9)(cid:136)(cid:5)

(cid:9)(cid:134)(cid:4)

(cid:9)IR

(cid:9)?$

(cid:3)o(cid:8)

(cid:9)!"

(cid:3)(cid:128)"

(cid:9)6(cid:5)

(cid:2)w=

(cid:9)S#

(cid:3)(cid:137)"

(cid:9)J(cid:26)

(cid:3)L(cid:8)

(cid:9)!"

(cid:7)^(cid:11)

(cid:9);=

(cid:9)i(cid:29)

(cid:3)(cid:25)>

(cid:3)(cid:128)>

(cid:3)J(cid:26)

(cid:3)A(cid:8)

(cid:9)kU

(cid:7)]2

(cid:8)(cid:22)(cid:4)

(cid:8)g>

(cid:9)g>

(cid:8)(cid:22)F

(cid:8)(cid:131)$

(cid:3)o(cid:8)

(cid:9)d>

(cid:8)f=

(cid:8)i"

(cid:9)(cid:137)(cid:4)

(cid:3)6U

(cid:9)]=

(cid:8)(cid:131)M

(cid:3)(cid:130)(cid:8)

(cid:9)~#

(cid:0)m#

(cid:9)(cid:138)=

(cid:9)i=

(cid:8)(cid:131)>

(cid:8)(cid:22)>

(cid:8)jM

(cid:3)(cid:130)(cid:8)

(cid:9)_=

(cid:9)kF

(cid:9)k"

(cid:9)1"

(cid:9)1"

(cid:9)o"

(cid:9)o.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)m"

(cid:9)o=

(cid:9)c#

(cid:9)ǱR

(cid:9)_F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)m#

(cid:9)1=

(cid:9)_=

(cid:9)k=

(cid:9)_F

(cid:9)a.

(cid:9)b(cid:8)

(cid:9)Ir

(cid:9)(cid:128)(cid:4)

(cid:9)(cid:22)(cid:5)

(cid:9)q(cid:4)

(cid:9)(cid:18)(cid:12)

(cid:9)sr

(cid:9)J(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:11)

(cid:9)s(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)J(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)g(cid:5)

(cid:9)q(cid:4)

(cid:9)Cp

(cid:9)|(cid:11)

(cid:9)s(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)Z"

(cid:0)-(cid:5)

(cid:3)u"

(cid:9)v(cid:29)

(cid:3)w"

(cid:3)~>

(cid:2)w(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)~"

YZ"

(cid:2)n#

(cid:9)n"

(cid:9)(cid:25)"

(cid:9)1"

(cid:2)QM

(cid:3)Q(cid:8)

(cid:9)D"

(cid:3)-"

(cid:3)L"

(cid:9)n#

(cid:3)n"

(cid:9)Z(cid:29)

Yu(cid:26)

(cid:3)s(cid:8)

(cid:9)?"

(cid:3)(cid:134)>

(cid:9)o=

(cid:3)(cid:131)=

(cid:9)a=

(cid:3)_F

(cid:9)?$

(cid:3)b(cid:8)

(cid:9)GR

(cid:9)a"

(cid:9)1(cid:29)

(cid:9)Q#

(cid:3)Z=

(cid:9)_=

(cid:9)i(cid:26)

(cid:9)A(cid:8)

(cid:9)I(cid:29)

(cid:8)^(cid:20)

(cid:3)j=

(cid:9)G(cid:26)

(cid:9)^=

(cid:9)kF

(cid:9)z(cid:26)

(cid:3)L(cid:8)

(cid:9)d}

(cid:8)-=

(cid:3)i(cid:4)

(cid:9)f(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)]=

(cid:9)i(cid:26)

(cid:3)^(cid:8)

(cid:9)(cid:10)#

(cid:8)Z(cid:4)

(cid:9)(cid:22)=

(cid:9)G#

(cid:9)~"

(cid:9)g(cid:29)

(cid:9)Q(cid:26)

(cid:3)s(cid:8)

(cid:9)kR

(cid:3)a(cid:4)

(cid:9)(cid:133)>

(cid:9)(cid:10)(cid:11)

(cid:8)s(cid:4)

(cid:9)(cid:22)=

(cid:9)?(cid:20)

(cid:3)(cid:130)(cid:8)

(v)

(cid:9)D"

(cid:3)f(cid:19)

(cid:9)o(cid:4)

(cid:9)(cid:10)"

(cid:9)v"

(cid:3)u"

(cid:9)wT

(cid:3)b(cid:8)

(w)

(cid:9)Z"

(cid:0)]"

(cid:9);"

(cid:9)n#

(cid:3)1"

(cid:9)~F

(cid:9){(cid:20)

(cid:3)Q(cid:8)

(x)

(cid:9)G(cid:26)

(cid:9)^#

(cid:9)DR

(cid:9)_"

(cid:3)o#

(cid:9)1R

(cid:9)?(cid:26)

(cid:3)<(cid:8)

(cid:9)?r

(cid:8)J"

(cid:9)|>

(cid:9)u"

(cid:3)(cid:10)>

(cid:9)b=

(cid:8)G(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)D"

(cid:9)A"

(cid:9)Q(cid:20)

(cid:9);(cid:4)

(cid:9)]#

(cid:9)ZR

(cid:9)?(cid:26)

(cid:9)<(cid:8)

(cid:9)(cid:10)p

(cid:8)(cid:128)>

(cid:9)(cid:25)=

(cid:3)?(cid:26)

(cid:9)A(cid:4)

(cid:9)(cid:10)>

(cid:9)(cid:128)[

(cid:3)(cid:130)(cid:8)

(cid:9)~>

(cid:0)]>

(cid:8)(cid:22)=

(cid:8)i>

(cid:3)f"

(cid:8)Z>

(cid:9)bM

(cid:3)j(cid:8)

(cid:9)Z#

(cid:0)~(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g"

(cid:9)(cid:22)"

(cid:9);M

(cid:3)Q(cid:8)

(cid:9)_"

(cid:7)](cid:19)

(cid:0);>

(cid:9)](cid:4)

(cid:8)(cid:22)}

(cid:9)ZF

(cid:0)i$

(cid:3)b(cid:8)

(cid:9)_"

(cid:9)m"

(cid:9)b"

(cid:9)b.

(cid:9)b"

(cid:9)mF

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)k"

(cid:9)Ǳ"

(cid:9)n"

(cid:9)1"

(cid:9)n"

(cid:9)1F

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)k=

(cid:9)z"

(cid:9)Ǳ=

(cid:9){"

(cid:9)mR

(cid:9){"

(cid:9)b.

(cid:9)o(cid:8)

exceptional knight’s cycles.

158. We conduct two censuses, ﬁrst to determine the maxima and unknown minima
and then to count the extreme solutions. Since extreme solutions are rare, the second
census needs to examine fewer than 2000 bunches. Most of the minima are obvious and
ﬁndable by hand; Jelliss proved (surprisingly) that at least two 90◦ moves are needed.
Proof. Suppose there’s a tour without any right-angle moves. We must make the
eight moves of class A in exercise 157. Edge 01
22 is also forced; otherwise we’d have
15 is forced,
20
because we can’t have 11
14
(and all of class C) is forced. The central wedges are now determined, giving us all of
class U. We must also have class B, because 13
32 makes a right angle. That forces
class M, which forces class E. It’s a nice kaleidoscopic pattern, with 8-fold symmetry;
but it’s not a tour! Sharper analysis shows that a single 90◦ angle is also impossible.

13. Similarly, all eight edges of class G are forced. Then 03

24; we must have all of class D. Hence 02

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

03

01

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:23)
(cid:20)
(cid:13)
(cid:21)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
p
(cid:12)
$
%
(cid:30)
’
(cid:14)
)
4
W
9
(cid:17)
Y
>
(cid:20)
T
O
8
V
9
:
(cid:0)
(cid:2)
(cid:29)
$
.
3
N
8
(cid:31)

*
P
(cid:7)
#
U
$
%
&
3
N
(
)

*
+
,
(cid:7)
#
(cid:19)
T
&
(cid:14)
/
)
(cid:16)
\
(cid:24)
:
(cid:0)
(cid:29)
p
.
&
(cid:30)
t
(cid:31)
4
0
5
(cid:2)
(cid:7)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
$
%
l
N
(
V
(cid:15)
*
\
5
Y
(cid:0)
.
N
O
8
*
P
(cid:0)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:19)
.
&
3
(cid:14)
t
(cid:31)
h
(cid:16)
0
(cid:17)
(cid:2)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
l
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:20)
@
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
r
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
(cid:13)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:4)
(cid:11)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
&
x
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
&
(cid:13)
(
0
(cid:0)
(cid:7)
(cid:3)
#
(cid:5)
(cid:19)
(cid:6)
(cid:14)
)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:29)
(cid:5)
.
&
(cid:30)
/
(cid:31)

0
(cid:2)
(cid:7)
(cid:3)
#
(cid:26)
$
%
’
)
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:26)
.
&
(cid:13)
/
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:5)
(cid:20)
(cid:6)
O
)
(cid:2)
(cid:8)
(cid:3)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
$
%
(cid:6)
’
(cid:14)
W
9
(cid:24)
Y
>
(cid:5)
(cid:26)
(cid:6)
(cid:13)
V
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
$
.
3
N
8
(cid:31)

*
P
(cid:7)
(cid:29)
$
%
@
3
N

*
9
,
(cid:7)
(cid:8)
(cid:26)
%
&
(cid:6)
(cid:13)
(
\
:
(cid:7)
(cid:29)
p
(cid:26)
(cid:30)
(cid:13)
(cid:31)
4
5
(cid:7)
(cid:8)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
U
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
V
h
e
9
(cid:17)
,
(cid:19)
M
7
N
x
8
(cid:31)
e
9
(cid:24)
Y
$
@
N
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:29)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
(cid:11)
%
3
(cid:31)
h
9
5
:
(cid:2)
(cid:7)
>
(cid:29)
(cid:11)
(cid:19)
M
%
&
3
N
x
(
(cid:31)
h
e
\
(cid:17)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
$
.
&
N
/
(cid:15)
*
0
5
P
(cid:0)
#
(cid:29)
(cid:19)
(cid:20)
3
x
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
#
T
&
/
)
\
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
$
%
@
’
(cid:14)
(cid:15)
W
9
(cid:17)
Y
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
l
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
(cid:26)
(cid:13)
)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
.
(cid:6)
8
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
p
(cid:30)
(cid:31)
4
5
(cid:2)
(cid:7)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
%
l
(cid:6)
(
)
\
:
(cid:2)
(cid:7)
(cid:26)
.
(cid:13)
8
(cid:15)
5
(cid:0)
(cid:7)
U
(cid:11)
(cid:20)
3
O
(cid:31)
h
5
(cid:2)
(cid:8)
M
%
(cid:129)
x
e
9
(cid:24)
Y
(cid:0)
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:26)
$
&
(cid:129)
(
(cid:31)
*
0
P
(cid:0)
(cid:7)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
(cid:31)
h
5
(cid:7)
(cid:8)
[
%
&
N
O
(
*
+
,
(cid:0)
(cid:29)
(cid:26)
&
3
(cid:13)
(

0
(cid:7)
(cid:3)
(cid:29)
(cid:5)
%
@
(cid:30)
)

9
:
(cid:2)
(cid:7)
(cid:8)
7
3
8

9
:
(cid:2)
(cid:7)
(cid:5)
(cid:19)
%
@
(cid:30)
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
&
(cid:129)
(
*
\
Y
(cid:0)
(cid:7)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
%
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
>
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
2
(cid:20)
%
3
O
)

9
:
(cid:2)
(cid:8)
(cid:19)
7
3
(cid:14)
8

(cid:16)
9
(cid:24)
:
(cid:11)
(cid:19)
%
@
(cid:14)
(cid:15)
(cid:16)
9
X
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:11)
(cid:26)
$
&
(cid:129)
(
V
(cid:15)
*
0
5
P
(cid:0)
M
.
&
N
O
/
)
*
0
P
(cid:0)
#
(cid:29)
.
3
8
)

(cid:2)
(cid:7)
(cid:3)
#
7
&
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
#
(cid:11)
.
&
/
)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:11)
(cid:20)
.
&
3
O
/
K
h
0
5
(cid:2)
T
N
O
8
*
9
,
(cid:0)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
‘
’
(
(cid:15)
*
+
5
,
(cid:0)
(cid:20)
@
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
%
l
N
(
(cid:15)
*
\
5
Y
(cid:0)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:20)
&
(cid:6)
O
(
(cid:15)
0
5
(cid:2)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
l
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:29)
p
(cid:20)
&
(cid:30)
O
(
(cid:31)
4
0
5
(cid:2)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
&
(cid:13)
(
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:20)
&
O
(
0
(cid:0)
(cid:2)
(cid:3)
(cid:26)
&
(cid:13)
(
0
(cid:0)
(cid:7)
(cid:3)
(cid:5)
&
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
r
&
H
(
(cid:31)
h
0
5
(cid:2)
(cid:7)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
&
N
(cid:14)
(
(cid:15)
e
+
(cid:17)
,
(cid:11)
(cid:19)
(cid:20)
&
(cid:21)
(
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
%
x
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:4)
(cid:11)
(cid:19)
(cid:14)
(cid:31)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
>
(cid:11)
(cid:19)
[
&
N
(cid:21)
(
(cid:31)
(cid:15)
W
0
X
P
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
&
’
(cid:14)
(
)
W
\
(cid:24)
Y
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:26)
$
.
&
(cid:129)
/
(cid:15)
*
0
5
P
(cid:0)
(cid:29)
(cid:26)
(cid:20)
3
(cid:13)
O
)

(cid:8)
(cid:3)
#
(cid:29)
7
3
8
)

9
:
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
T
&
H
/
V

\
:
(cid:2)
(cid:7)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
@
(cid:13)
)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:29)
.
3
8

(cid:2)
(cid:7)
(cid:3)
(cid:26)
%
‘
3
(cid:13)
(

+
:
(cid:7)
(cid:5)
%
(cid:6)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:19)
(cid:30)
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
%
(cid:6)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:29)
r
(cid:26)
H
(cid:13)
(cid:31)
h
5
(cid:7)
(cid:8)
[
%
N
O
*
9
,
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
(cid:14)
W
9
(cid:24)
Y
(cid:0)
>
(cid:26)
(cid:13)
V
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
$
.
3
N
8
(cid:31)
h
*
5
P
>
[
%
&
N
O
(
(cid:31)
*
+
,
(cid:0)
$
@
(cid:6)
N
*
P
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
(cid:30)
K

(cid:2)
(cid:7)
(cid:8)
(cid:3)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
T
8
9
:
(cid:0)
(cid:2)
(cid:7)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
@
(cid:13)
(cid:14)
(cid:31)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:5)
$
(cid:6)
N
(cid:31)
*
P
(cid:7)
(cid:8)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:4)
(cid:19)
(cid:20)
%
(cid:21)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:19)
.
@
3
(cid:14)
8
(cid:31)
4
(cid:16)
X
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:12)
$
%
&
’
(cid:14)
(
V
W
\
(cid:24)
Y
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
(cid:28)
(cid:26)
&
(cid:13)
(
V
0
(cid:0)
(cid:7)
(cid:3)
$
.
&
(cid:6)
N
/
*
0
P
(cid:7)
#
U
3
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
p
(cid:19)
T
&
(cid:30)
(cid:14)
/
V
4
(cid:16)
\
(cid:17)
:
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
%
@
)
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
.
@
3
(cid:14)
8
4
(cid:16)
X
(cid:2)
(cid:20)
%
(cid:6)
O
9
:
(cid:2)
(cid:8)
(cid:4)
@
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:19)
$
N
(cid:14)
(cid:15)
e
(cid:17)
P
(cid:0)
>
(cid:20)
&
O
(
V
0
(cid:0)
(cid:2)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
(cid:129)
(cid:14)
(cid:15)
e
X
P
(cid:0)
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
(cid:5)
.
(cid:6)
8
(cid:31)
(cid:2)
(cid:7)
(cid:3)
(cid:4)
$
N
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:4)
(cid:19)
l
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
(cid:19)
.
(cid:6)
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:2)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
#
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
%
‘
(
)
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:19)
.
(cid:6)
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:2)
(cid:4)
(cid:20)
O
(cid:31)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:19)
$
@
N
(cid:14)
W
(cid:24)
P
(cid:0)
#
(cid:23)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:5)
.
&
(cid:6)
/
K
0
(cid:2)
(cid:7)
(cid:3)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
’
(cid:15)
*
5
P
(cid:0)
(cid:7)
>
(cid:26)
(cid:20)
&
(cid:13)
O
(
V
0
(cid:0)
(cid:3)
$
.
(cid:6)
N
8
*
P
(cid:7)
2
@
3
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
7
(cid:6)
(cid:14)
8
)
(cid:16)
9
(cid:24)
:
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
l
3
N
(cid:14)
(
4
W
\
X
(cid:19)
(cid:20)
%
(cid:21)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:4)
(cid:11)
(cid:19)
@
(cid:14)
(cid:31)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
M
N
x
(cid:15)
e
(cid:17)
P
(cid:0)
>
(cid:4)
(cid:20)
O
K
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
(cid:31)
4
W
X
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
l
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
(cid:28)
(cid:29)
.
&
3
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
T
&
N
/
*
\
,
(cid:0)
(cid:7)
(cid:29)
(cid:5)
(cid:19)
(cid:30)
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
#
(cid:26)
%
&
(cid:13)
(
)
\
:
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
$
%
@
N
(cid:14)
W
9
(cid:24)
Y
(cid:0)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:26)
3
(cid:13)
V

(cid:7)
(cid:8)
(cid:3)
$
7
N
8
*
9
Y
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:12)
@
3
(cid:13)
(cid:14)
)

(cid:16)
(cid:24)
(cid:8)
(cid:26)
7
(cid:13)
8
)
9
:
(cid:0)
(cid:7)
U
.
3
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
(cid:12)
$
%
’
(cid:14)
W
9
(cid:24)
Y
(cid:0)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:26)
3
(cid:13)
K

(cid:7)
(cid:8)
(cid:3)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
2
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:12)
%
3
(cid:13)
(cid:14)
)

(cid:16)
9
(cid:24)
:
7
(cid:6)
8
9
:
(cid:2)
(cid:7)
(cid:29)
(cid:26)
3
(cid:13)

(cid:7)
(cid:8)
(cid:3)
(cid:5)
%
@
(cid:6)
)
9
:
(cid:2)
(cid:7)
(cid:8)
2
.
3
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
(cid:5)
(cid:19)
$
%
(cid:6)
N
(cid:14)
e
9
(cid:24)
,
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:129)
)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
U
.
3
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
(cid:12)
$
%
’
(cid:14)
W
9
(cid:24)
Y
(cid:0)
(cid:5)
(cid:26)
(cid:6)
(cid:13)
(cid:31)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
@
H
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:29)
(cid:20)
%
@
3
O
)

9
:
(cid:2)
(cid:8)
U
T
3
8
(cid:31)

9
:
(cid:2)
(cid:7)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:20)
(cid:13)
(cid:21)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:26)
$
&
(cid:129)
(
V
*
0
P
(cid:0)
(cid:7)
#
(cid:29)
$
.
&
3
N
/
)

*
0
P
(cid:7)
#
(cid:29)
T
&
3
/
)

\
:
(cid:2)
(cid:7)
(cid:29)
7
&
3
t

+
:
(cid:2)
(cid:7)
U
%
&
3
(

+
:
(cid:2)
(cid:7)
r
(cid:23)
%
&
H
(cid:13)
(cid:14)
(
h
(cid:16)
+
X
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
(cid:14)
W
9
(cid:24)
Y
(cid:0)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
%
&
(cid:30)
(
K

\
:
(cid:2)
(cid:7)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
’
)
*
9
,
(cid:0)
(cid:7)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
p
(cid:19)
(cid:30)
(cid:14)
(cid:31)
4
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:12)
[
%
’
(cid:21)
(cid:15)
W
9
(cid:17)
,
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
’
(cid:15)
*
9
5
,
(cid:0)
(cid:7)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:28)
(cid:29)
&
3
(
V

0
(cid:2)
(cid:7)
(cid:3)
$
T
l
N
/
)
*
\
,
(cid:0)
(cid:7)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
(cid:19)
(cid:30)
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
l
(cid:129)
(
(cid:15)
*
\
5
Y
(cid:0)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
V

(cid:16)
(cid:24)
(cid:2)
(cid:8)
7
@
N
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
%
‘
3
(
h
+
5
:
(cid:2)
(cid:11)
(cid:19)
(cid:20)
%
3
x
4
(cid:16)
9
X
:
(cid:2)
(cid:11)
(cid:19)
(cid:20)
%
(cid:21)
(cid:15)
(cid:16)
9
(cid:17)
:
(cid:0)
(cid:2)
(cid:4)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:31)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
[
N
(cid:21)
(cid:31)
(cid:15)
W
X
P
(cid:0)
>
(cid:19)
M
N
x
K
e
(cid:24)
P
(cid:0)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
p
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:26)
$
%
&
3
(cid:129)
(
)

*
\
Y
(cid:7)
(cid:5)
7
&
(cid:6)
t
)
+
:
(cid:2)
(cid:7)
U
(cid:11)
.
3
8
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:19)
M
%
N
x
e
9
(cid:24)
Y
(cid:0)
}
(cid:26)
&
(cid:13)
(
K
0
(cid:0)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
$
.
&
H
N
t
V

*
0
P
(cid:7)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:20)
O
(cid:31)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:26)
$
&
(cid:129)
(
*
0
P
(cid:0)
(cid:7)
U
@
3
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
T
(cid:14)
8
(cid:16)
9
(cid:24)
:
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
@
3
(cid:14)
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:19)
.
3
(cid:14)
8

(cid:16)
(cid:24)
(cid:2)
(cid:19)
%
@
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:4)
(cid:19)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
#
(cid:12)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:26)
.
(cid:13)
8
)
(cid:0)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
.
H
8
)

(cid:2)
(cid:7)
(cid:3)
(cid:4)
T
8
)
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:19)
.
(cid:6)
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:2)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:26)
$
%
&
(cid:6)
(cid:129)
(
)
*
\
Y
(cid:7)
2
.
3
8
)

(cid:2)
(cid:7)
(cid:3)
(cid:19)
7
(cid:6)
(cid:14)
8
(cid:16)
9
(cid:24)
:
>
(cid:11)
(cid:26)
(cid:13)
(cid:31)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
[
N
O
*
P
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
(cid:26)
&
H
(cid:13)
(
V

0
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:31)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
M
N
x
(cid:15)
e
(cid:17)
P
(cid:0)
}
(cid:29)
(cid:20)
3
O
K

(cid:2)
(cid:8)
(cid:3)
$
7
&
N
t
*
+
Y
(cid:0)
(cid:7)
(cid:11)
(cid:19)
@
3
(cid:14)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
%
3
x
(cid:31)
4
(cid:16)
9
X
:
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
l
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:29)
(cid:5)
$
%
&
(cid:30)
N
(
V

*
\
Y
(cid:7)
(cid:29)
$
T
&
3
N
/

*
\
,
(cid:7)
(cid:29)
(cid:26)
%
&
3
(cid:13)
(

\
:
(cid:7)
(cid:11)
(cid:26)
%
&
(cid:13)
(
(cid:15)
\
5
:
(cid:0)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
>
(cid:29)
(cid:5)
(cid:20)
&
H
O
(
V

0
(cid:2)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
$
@
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:29)
$
@
3
N

*
P
(cid:7)
(cid:8)
#
(cid:29)
%
3

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:26)
%
&
(cid:13)
(
\
:
(cid:0)
(cid:7)
(cid:26)
&
(cid:13)
(
0
(cid:0)
(cid:7)
(cid:3)
>
(cid:29)
p
(cid:19)
(cid:30)
(cid:14)
(cid:31)
4
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
$
@
N
(cid:14)
W
(cid:24)
P
(cid:0)
(cid:11)
(cid:19)
@
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:26)
%
3
(cid:13)

9
:
(cid:7)
(cid:8)
(cid:4)
(cid:19)
%
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:5)
(cid:19)
&
(cid:6)
(cid:14)
(
V
(cid:16)
0
(cid:24)
(cid:2)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:19)
$
@
N
(cid:14)
)
(cid:15)
W
X
P
(cid:0)
(cid:20)
.
&
O
/
)
0
(cid:0)
(cid:2)
(cid:3)
(cid:29)
.
3
8

(cid:2)
(cid:7)
(cid:3)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:26)
(cid:6)
(cid:13)
)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
.
(cid:6)
8
V
(cid:2)
(cid:7)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
‘
’
(
)
(cid:15)
*
0
5
P
(cid:0)
(cid:20)
.
O
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:20)
3
O
4
5
(cid:2)
(cid:8)
(cid:26)
(cid:20)
%
3
(cid:13)
O

9
:
(cid:8)
(cid:5)
(cid:26)
%
(cid:6)
(cid:13)
(cid:31)
9
:
(cid:7)
(cid:8)
(cid:5)
(cid:26)
$
(cid:6)
’
(cid:31)
*
P
(cid:7)
(cid:8)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
l
N
(cid:14)
(
(cid:15)
W
\
X
Y
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:20)
&
3
O
(
4
0
5
(cid:2)
(cid:29)
(cid:11)
(cid:20)
%
3
O
4
9
5
:
(cid:2)
2
(cid:11)
(cid:20)
%
3
O
(cid:31)
4
9
5
:
(cid:2)
(cid:29)
(cid:11)
(cid:19)
[
%
@
3
N
(cid:21)
(cid:31)
4
W
9
X
,
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:20)
(cid:13)
x
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:26)
(cid:6)
(cid:13)
(cid:15)
5
(cid:7)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:12)
$
%
&
’
(cid:14)
(
V
W
\
(cid:24)
Y
$
.
&
(cid:6)
N
/
*
0
P
(cid:7)
}
(cid:29)
(cid:26)
3
(cid:13)
K

(cid:7)
(cid:8)
(cid:3)
(cid:5)
$
7
&
(cid:30)
N
t

*
+
Y
(cid:7)
#
2
%
3
)

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:29)
r
(cid:19)
7
&
H
(cid:14)
t
(cid:31)
h
(cid:16)
+
X
:
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
%
@
(cid:6)
)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:29)
(cid:11)
.
@
3
8
(cid:31)
4
5
(cid:2)
(cid:7)
M
%
N
O
*
9
Y
(cid:0)
(cid:8)
>
@
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
$
N
*
P
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
&
(cid:30)
(
K

0
(cid:2)
(cid:7)
(cid:3)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
(cid:129)
(cid:14)
(cid:31)
(cid:15)
e
X
P
(cid:0)
[
&
N
O
(
*
0
P
(cid:0)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
@
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
>
(cid:19)
(cid:20)
(cid:21)
(cid:31)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
#
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
%
‘
(
)
+
:
(cid:0)
(cid:2)
(cid:7)
.
@
(cid:14)
8
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:12)
(cid:13)
(cid:14)
V
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
$
.
&
(cid:6)
N
/
)
*
0
P
(cid:7)
(cid:29)
(cid:5)
.
H
8
)

(cid:2)
(cid:7)
(cid:3)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
(cid:6)
’
(cid:15)
*
5
P
(cid:7)
(cid:5)
(cid:20)
(cid:6)
O
)
(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
(cid:4)
(cid:5)
$
%
(cid:6)
N
)
*
9
Y
(cid:7)
(cid:8)
(cid:19)
.
@
(cid:14)
8
(cid:31)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
>
p
$
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
[
(cid:129)
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
l
N
(cid:14)
(
(cid:31)
(cid:15)
W
\
X
Y
(cid:4)
(cid:11)
(cid:19)
M
N
x
(cid:31)
(cid:15)
e
(cid:17)
P
(cid:0)
>
(cid:19)
[
N
(cid:21)
(cid:31)
W
(cid:24)
P
(cid:0)
(cid:4)
$
@
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
#
(cid:4)
(cid:19)
$
N
(cid:14)
)
e
(cid:24)
P
(cid:0)
(cid:29)
(cid:11)
(cid:19)
.
‘
3
(cid:14)
/
(cid:31)
4
(cid:16)
0
X
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
l
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
2
(cid:19)
$
%
&
3
N
(cid:14)
(
)

W
\
(cid:24)
#
(cid:19)
7
&
(cid:14)
t
)
(cid:16)
+
(cid:24)
:
(cid:0)
(cid:11)
.
&
/
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:26)
(cid:20)
&
(cid:13)
O
(
)
0
(cid:0)
(cid:3)
#
(cid:29)
(cid:11)
.
3
8
)
4
5
(cid:2)
(cid:7)
>
(cid:29)
(cid:11)
(cid:20)
T
&
3
O
/
V
4
\
5
:
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
.
8
)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:20)
.
&
3
O
/

0
(cid:2)
(cid:3)
(cid:4)
%
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
#
(cid:11)
(cid:19)
&
(cid:14)
(
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
(cid:20)
&
O
(
0
(cid:0)
(cid:2)
(cid:3)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
N
(cid:14)
(cid:15)
W
X
P
(cid:0)
(cid:19)
(cid:20)
&
x
(
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
(cid:20)
&
x
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
.
3
x
8
4
(cid:16)
X
(cid:2)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
‘
N
(cid:14)
(
)
(cid:15)
e
0
(cid:17)
P
(cid:19)
(cid:20)
.
(cid:21)
8
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:28)
.
8
V
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
#
(cid:4)
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:11)
(cid:19)
.
&
3
(cid:14)
t
)
h
(cid:16)
0
(cid:17)
(cid:2)
7
O
8
9
:
(cid:0)
(cid:2)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
l
(cid:13)
(
)
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:11)
(cid:20)
.
O
8
)
(cid:15)
5
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
&
(cid:6)
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:2)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
&
N
(cid:14)
(
(cid:15)
W
\
X
Y
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
(cid:20)
x
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
.
3
x
8
V
4
(cid:16)
X
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:26)
$
&
(cid:129)
(
V
*
0
P
(cid:0)
(cid:7)
(cid:26)
$
.
&
(cid:129)
/
)
*
0
P
(cid:0)
(cid:7)
(cid:28)
(cid:29)
.
3
8
V

(cid:2)
(cid:7)
(cid:3)
$
T
&
N
/
*
\
,
(cid:0)
(cid:7)
}
U
&
3
(
K

0
(cid:2)
(cid:7)
(cid:3)
r
(cid:19)
$
7
&
H
N
(cid:14)
t
h
W
+
X
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
$
%
@
3
’
(cid:14)
h
W
9
(cid:17)
Y
%
@
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
‘
3
(
K

0
(cid:2)
(cid:7)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
N
(
)
*
\
Y
(cid:0)
(cid:7)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
2
p
(cid:19)
(cid:30)
(cid:14)
(cid:31)
4
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:12)
[
%
’
(cid:21)
(cid:15)
W
9
(cid:17)
,
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:29)
p
(cid:19)
(cid:30)
(cid:14)
4
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:29)
&
3
(
V

0
(cid:2)
(cid:7)
(cid:3)
$
T
l
N
/
)
*
\
,
(cid:0)
(cid:7)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:5)
&
(cid:6)
(
V
0
(cid:2)
(cid:7)
(cid:3)
$
.
’
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
$
%
(cid:6)
’
(cid:14)
(cid:15)
W
9
(cid:17)
Y
(cid:26)
(cid:20)
(cid:13)
O
(cid:31)
(cid:0)
(cid:8)
(cid:3)
(cid:5)
$
(cid:6)
N
*
P
(cid:7)
(cid:8)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
r
(cid:23)
H
(cid:13)
(cid:14)
(cid:31)
h
(cid:16)
X
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
2
(cid:11)
$
%
l
3
N
(
K
4
*
\
5
Y
[
T
N
(cid:21)
8
W
9
(cid:24)
,
2
(cid:11)
@
3
(cid:31)
4
5
(cid:2)
(cid:7)
(cid:8)
(cid:19)
[
%
N
(cid:21)
W
9
(cid:24)
,
(cid:0)
U
(cid:11)
(cid:19)
3
(cid:14)
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:19)
M
%
&
N
x
(
K
e
\
(cid:24)
Y
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
gallery of knight’s tours
acute angles
obtuse angles
orthogonal angles
diagonal angles
axial angles
lateral angles, see axial
Historical notes
Secker
Onitiu
Murray
Stappers
unique
star
history
de Laisement
Laisement
de Jaenisch
Hansson
variance

86

ANSWERS TO EXERCISES

7.2.2.4

Each of the six possible angles α can occur surprisingly often in a single tour.
Their maxima, (29, 30, 39, 33, 25, 19), are achieved respectively (136, 432, 48, 176, 32,
112) times among the 13 trillion solutions, and examples appear in (g), (h), (i), (j), (k),
(l) of Fig. A–19. On the other hand the minima, namely (4, 0, 2, 0, 0, 0), aren’t diﬃcult
to achieve, except for Jelliss’s construction in Fig. A–19(p); they occur respectively
(4073251792, 193895168, 1152, 316388348, 312777068, 196464725912) times.

It’s also interesting to group angles together into acute angles (< 90◦), obtuse
angles (> 90◦), and orthogonal angles (90◦ or 180◦). These groups can occur as many
as (42, 47, 42) times, while their minima are (4, 4, 4). (See Fig. A–19(m, n, o) and
(s, t, u).) The maxima occur (56, 464, 7128) times, and the minima are also fairly rare:
(28068, 4, 400624). Indeed, Fig. A–19(n) is essentially unique.

·

θ

}

{

≈

−

−

±

≈

6θ

10θ

90◦

θ, 180◦

4458.8◦ and 84

Connoisseurs also group together the diagonal angles

and the axial
angles 90◦
θ, which occur at least (4, 4) and at most (39, 46) times. Those extremes,
achieved in (300312, 1964, 344, 80) ways, are exhibited in Fig. A–19(m), (q), (v), (w).
90◦ +
The least and greatest sums of all angles are 52
7928.7◦, illustrated in Fig. A–19(d) and (e), achievable in just 88 and 64 ways.
Historical notes: Problems 1 and 2 in Jelliss’s magazine [Chessics 1, 1 (Walton on
Naze, March 1976), 2] asked only for the six maxima and minima; now at last we can
ask and solve the more detailed questions. Only two of the maxima had been known
before 2025. Prior to that, the best published constructions were (26, 38, 30, 22) for
(θ, 90◦, 90◦+θ, 180◦
θ) [G. P. Jelliss, in Chessics 1, 5 (July 1978), 4–5; J. Recreational
Math. 27 (1995), 237], and 26 for 90◦
θ [J. J. Secker, in Chessics 1, 7 (March 1979),
10]. Astonishingly, a tour achieving the correct value 19 for 180◦ had already been
given by V. Onitiu in The Problemist: Fairy Chess Supplement 1, 12 and 13 (June and
August, 1932), pages 74 and 82! And H. J. R. Murray, on page 79 of an unpublished
manuscript [The Knight’s Problem (Oxford: Bodleian Library, 1942), viii + 283 pages],
had found the “herringbone” tour of Fig. A–19(h), actually in another context.

−

−

·

t

≤

≤

159. (Solution by Filip Stappers.) The maximum number of cells that can be tarnished
t times turns out to be respectively (20, 32, 46, 24, 20, 12, 6, 4) for t = (0, 1, . . . , 7).
Figure A–20 exhibits champion tours that achieve those maxima, symmetrically when
5: They occur only (9748,
possible. Such winners are rare gems, especially when 1
16, 8, 56, 4, 28, 372348, 904604) times, respectively, among the 13 trillion possible tours.
(Indeed, the solutions for t = 2 and t = 4 are unique, except for rotation and reﬂection.)
A cell that’s tarnished by seven of its neighbors is called a star, and 4-star cycles
have an interesting history. One of the ﬁrst major treatises on knight’s tours, Balli`ere
de Laisement’s 74-page Essai sur les Probl´emes de Situation (Rouen, 1782), presented
the 4-star tour of Fig. A–20(j) as his second example of how to construct a solution
“mechanically” (pages 16–20). He also found a diﬀerent 4-star tour (Planche A#5).
C. F. de Jaenisch [Trait´e des applications de l’analyse math´ematique au jeu des ´echecs
96; Pl. IV, Fig. 7] presented Fig. A–20(h), the ﬁrst known symmetrical
2 (1862),
example. And F. Hansson [Fairy Chess Review 6, 111 (February 1948), solution (iv) to
problem 7531] presented Fig. A–20(i), a symmetrical example with only two of the four
stars adjacent to a corner. The four cells adjacent to a corner are always tarnished at
least four times. It turns out that 2517414323 tours have no cell tarnished more than
four times, among which 2213509 have only those four cells quadruply tarnished.

§

The sum of all tarnish counts is 128 in every knight’s cycle; hence the mean is
always exactly 2. What about the variance? Answer: The sum of squares is always at
least 308 and at most 478 — achieved in 152 and 64 ways, such as Fig. A–20(k) and (l).

December 4, 2025

7.2.2.4

ANSWERS TO EXERCISES

87

(a)
02200220
25334352
05302242
03300320
02300330
24220350
25343352
02200220

(d)
02101220
26333362
13311330
13300330
03300331
03311331
26333362
02210120

(g)
02211220
26223362
13100031
03632221
12223630
13000131
26332262
02211220

(j)
02101120
27312372
13233221
13022131
13122131
12233221
27311372
02111120

(cid:9)I(cid:4)

(cid:9)(cid:18)r

(cid:9)|(cid:5)

(cid:9)|(cid:4)

(cid:9)C(cid:4)

(cid:9)Cr

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:18)(cid:5)

(cid:9)|(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)r

(cid:9)(cid:128)(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)Ir

(cid:9)J(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)|(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)~"

YD"

(cid:9)L>

(cid:3)6#

(cid:8)!"

(cid:3)Z"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)(cid:10)"

(cid:8)D"

(cid:3)Q"

(cid:9)1(cid:26)

(cid:3)<"

(cid:9)Z"

(cid:2);(cid:26)

(cid:3)<(cid:8)

(cid:9)~"

(cid:0)-#

(cid:3)n"

(cid:9)-"

(cid:9)n"

(cid:9)1"

(cid:9)u(cid:26)

(cid:3)<(cid:8)

(cid:9)d"

(cid:9)](cid:19)

(cid:0);=

(cid:9)zR

(cid:9)z(cid:4)

(cid:7)6F

(cid:9)i$

(cid:3)o(cid:8)

(cid:9)~F

(cid:9)d"

(cid:9)o(cid:20)

(cid:9);#

(cid:9)~(cid:4)

(cid:9)fF

(cid:9)(cid:131).

(cid:9)b(cid:8)

(cid:9)I"

(cid:9)v"

(cid:9)w(cid:20)

(cid:9)Q#

(cid:9)Z"

(cid:9)(cid:10)"

(cid:9)<(cid:20)

(cid:9)Q(cid:8)

(cid:9)(cid:10)"

(cid:8)->

(cid:9)(cid:133)(cid:5)

(cid:8)(cid:128)(cid:5)

(cid:9)(cid:128)"

(cid:9)Z"

,u(cid:26)

(cid:9)<(cid:8)

(b)
01211120
16433362
14111131
13113141
14113131
14111131
26233561
02111210

(cid:9)!F

(cid:3)a$

(cid:3)b=

(cid:9)?#

(cid:3)m=

(cid:9)dR

(cid:9)GT

(cid:3)o(cid:8)

(cid:9)I(cid:4)

(cid:8)f(cid:19)

(cid:9)j=

(cid:9)E(cid:4)

(cid:8)(cid:18)(cid:4)

(cid:9)gF

(cid:9)GM

(cid:3)Q(cid:8)

(cid:9)D"

(cid:7)(cid:135)"

(cid:9)Q#

(cid:9)n"

(cid:3)A"

(cid:9)1"

(cid:9)w$

(cid:3)o(cid:8)

(cid:9)!>

(cid:7)^(cid:26)

(cid:3)(cid:25)=

(cid:9)?(cid:4)

(cid:3)(cid:18)(cid:4)

(cid:9)I>

(cid:9)JM

(cid:3)j(cid:8)

(c)
02122220
26222242
12212022
22225222
22222222
12222222
25422442
02200220

(cid:9)G"

(cid:3)^(cid:29)

(cid:9)b(cid:4)

(cid:3)(cid:22)r

(cid:9)J(cid:26)

(cid:9)(cid:25)=

(cid:9)G(cid:26)

(cid:3)A(cid:8)

(cid:9)?#

(cid:3)-=

(cid:9)?#

(cid:9)(cid:138)"

(cid:3)|(cid:26)

(cid:3)<=

(cid:9)G(cid:26)

(cid:3)A(cid:8)

(cid:9)G#

(cid:3)Ǳ(cid:28)

(cid:9)D=

(cid:3)S=

(cid:9)G(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)^(cid:8)

(cid:9)?(cid:11)

(cid:8)A>

(cid:9)|(cid:26)

(cid:3)A=

(cid:9)G(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)^(cid:8)

(cid:9)E"

(cid:8)](cid:29)

(cid:9);"

(cid:3)j>

(cid:3)(cid:133)=

(cid:8)E"

(cid:9)(cid:130)M

(cid:3)Q(cid:8)

(cid:9)Z2

Y](cid:19)

(cid:8)(cid:130)=

(cid:9)d(cid:4)

(cid:8)g"

(cid:9)~"

(cid:0);$

(cid:3)o(cid:8)

(cid:9)~(cid:4)

(cid:0)]=

(cid:9)iM

(cid:3)j=

(cid:9)d(cid:4)

(cid:8)]=

(cid:9)iM

(cid:3)(cid:130)(cid:8)

(cid:9)k"

(cid:9)mF

(cid:9){=

(cid:9){#

(cid:9)Ǳ"

(cid:9)ǱF

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)_F

(cid:9)z"

(cid:9)n=

(cid:9){"

(cid:9)mF

(cid:9)c"

(cid:9)o.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)mF

(cid:9){.

(cid:9)b=

(cid:9)k"

(cid:9)ǱF

(cid:9)c.

(cid:9)b(cid:8)

Jelliss
author

(cid:9)I(cid:4)

(cid:9)C(cid:12)

(cid:9)s(cid:5)

(cid:9)(cid:128)(cid:4)

(cid:9)C(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)I(cid:11)

(cid:9)(cid:25)(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:11)

(cid:9)s(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:10)(cid:5)

(cid:9)(cid:128)p

(cid:9)J(cid:11)

(cid:9)sp

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)~"

Y(cid:128)"

(cid:3)u(cid:28)

(cid:3)n#

(cid:3)D"

(cid:9)~"

(cid:9)QM

(cid:3)Q(cid:8)

(cid:9)I"

(cid:8)-"

(cid:9)n"

(cid:3)1#

(cid:9)n"

(cid:9)!"

(cid:3)Q(cid:26)

(cid:3)<(cid:8)

(cid:9)(cid:10)"

(cid:8)(cid:128)"

(cid:9)Q"

(cid:3)n(cid:28)

(cid:3)1#

(cid:3)Z>

(cid:9)J(cid:26)

(cid:3)s(cid:8)

(cid:9)GF

(cid:3)a=

(cid:7){=

(cid:3)i}

(cid:9)Ǳ#

(cid:7)ZF

(cid:9)(cid:131).

(cid:9)b(cid:8)

(cid:9)d#

(cid:8)~(cid:11)

(cid:9)j(cid:20)

(cid:9)(cid:130)#

(cid:9)Z(cid:4)

(cid:9)]"

(cid:9)|(cid:20)

(cid:9)Q(cid:8)

(cid:9)~"

(cid:9)Ǳ"

(cid:9)u(cid:20)

(cid:9);#

(cid:9)D"

(cid:9)!"

(cid:9)Q(cid:26)

(cid:3)<(cid:8)

(cid:9)I"

(cid:9)v>

(cid:9);(cid:5)

(cid:3)|(cid:28)

(cid:9)->

(cid:3)C(cid:29)

(cid:8)J(cid:26)

(cid:3)A(cid:8)

(e)
01221220
24441441
24000241
12044042
24044021
14200042
14414442
02212210

(cid:9)d"

(cid:8)^=

(cid:9)c(cid:5)

(cid:9)(cid:134)#

(cid:9)-=

(cid:9)d=

(cid:8)G(cid:26)

(cid:3)s(cid:8)

(cid:9)?"

(cid:3)^(cid:4)

(cid:9)(cid:133)>

(cid:9)(cid:10)(cid:11)

(cid:8)(cid:25)#

(cid:9)(cid:137)F

(cid:9)z(cid:26)

(cid:3)L(cid:8)

(cid:9)Er

(cid:8)(cid:128)#

(cid:9)(cid:138)F

(cid:9)k"

(cid:3)o(cid:4)

(cid:9)6=

(cid:9)?(cid:26)

(cid:3)^(cid:8)

(cid:9)_"

(cid:3)A(cid:11)

(cid:7)<=

(cid:9)i(cid:5)

(cid:9)(cid:135)(cid:4)

(cid:9)(cid:18)F

(cid:9)?(cid:26)

(cid:3)<(cid:8)

(f)
01111110
25355352
25100252
12211310
01311221
25200152
25355352
01111110

(cid:9)_"

(cid:3)^=

(cid:3){=

(cid:9)z=

(cid:9)a#

(cid:9)mR

(cid:3)i$

(cid:3)o(cid:8)

(cid:9)d(cid:4)

(cid:8)f(cid:4)

(cid:9)](cid:4)

(cid:9)g#

(cid:9)~=

(cid:9)E=

(cid:9)(cid:131)(cid:26)

(cid:9)A(cid:8)

(cid:9)G"

(cid:9)v"

(cid:9)L"

(cid:9)Q"

(cid:9)1"

(cid:9)u"

(cid:9)w(cid:26)

(cid:3)<(cid:8)

(cid:9)(cid:10)#

(cid:8)-(cid:5)

(cid:3)q(cid:5)

(cid:9)J(cid:5)

(cid:9)(cid:128)>

(cid:9)C=

(cid:8)?(cid:26)

(cid:3)s(cid:8)

(cid:9)~"

(cid:0)~(cid:11)

(cid:9)Q>

(cid:9)(cid:130)2

(cid:3)(cid:22)2

(cid:8)]R

(cid:8)zM

(cid:3)Q(cid:8)

(cid:9)d#

(cid:8)~(cid:11)

(cid:2)j(cid:4)

(cid:9)(cid:22)>

(cid:9)g(cid:4)

(cid:8)(cid:22)R

(cid:9)i$

(cid:3)b(cid:8)

(cid:9)_R

(cid:7)a>

(cid:9);>

(cid:8)g>

(cid:8)(cid:22)#

(cid:8)~R

(cid:9)z$

(cid:3)o(cid:8)

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1=

(cid:9){=

(cid:9)zR

(cid:9)_F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)kF

(cid:9)_"

(cid:9)n#

(cid:9)1F

(cid:9)k"

(cid:9)bR

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)k#

(cid:9)m=

(cid:9)_=

(cid:9)aR

(cid:9)z"

(cid:9)oR

(cid:9){.

(cid:9)b(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:5)

(cid:9)|(cid:4)

(cid:9)I(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:11)

(cid:9)s(cid:5)

(cid:9)|(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:10)r

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)Ip

(cid:9)|(cid:11)

(cid:9)s(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:18)p

(cid:9)(cid:128)(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)~"

(cid:0)v"

(cid:9)Q"

(cid:9)n(cid:28)

(cid:3)n"

(cid:3)~"

(cid:9)uM

(cid:3)Q(cid:8)

(cid:9)~"

Yv"

(cid:3)Q>

(cid:9)u#

(cid:3)-"

(cid:9)Z"

PwM

(cid:3);(cid:8)

(cid:9)D"

(cid:3)~"

PnM

(cid:3)Q(cid:29)

(cid:9)J"

(cid:3)Z"

(cid:2)u[

(cid:3);(cid:8)

(cid:9)_"

(cid:3)(cid:134)(cid:11)

(cid:9)<(cid:26)

(cid:9)s(cid:26)

(cid:9)A#

(cid:9)ǱR

(cid:9)?$

(cid:3)b(cid:8)

(cid:9)G(cid:28)

(cid:9)~2

,gU

(cid:8)(cid:22)(cid:4)

(cid:8)Cr

(cid:9)J>

(cid:9)sM

(cid:3)(cid:130)(cid:8)

(cid:9)D=

(cid:3)_F

(cid:9)aF

(cid:9){"

(cid:3)n"

(cid:7)1[

(cid:3)Q(cid:26)

(cid:9)A(cid:8)

(cid:9)I(cid:11)

(cid:8)^(cid:5)

(cid:9)|=

(cid:9)G=

(cid:9)_=

(cid:9)d(cid:29)

(cid:9)(cid:135)(cid:26)

(cid:3)s(cid:8)

(h)
02200220
27322372
13022131
03321330
03312330
13122031
27322372
02200220

(cid:9)_R

(cid:3)a(cid:26)

(cid:9)<=

(cid:9)(cid:136)(cid:4)

(cid:3)f#

(cid:9)DR

(cid:9)z$

(cid:3)o(cid:8)

(cid:9)EU

(cid:9)(cid:10)2

(cid:8)(cid:22)=

(cid:8)d(cid:4)

(cid:9)f"

(cid:9)C(cid:11)

(cid:0)L(cid:20)

(cid:9)j(cid:8)

(cid:9)!F

(cid:9)ER

(cid:0){"

(cid:9)w"

(cid:9)<"

(cid:3)n"

(cid:3)o(cid:26)

(cid:9)L(cid:8)

(cid:9)(cid:10)p

(cid:8)(cid:128)"

(cid:9)(cid:130)>

(cid:9)w=

(cid:3)S=

(cid:9)d(cid:29)

(cid:9)J(cid:26)

(cid:3)s(cid:8)

(i)
02210120
14731372
12212131
14211231
13211241
13121221
27313741
02101220

(cid:9)(cid:10)#

(cid:8)ǱF

(cid:9)a(cid:29)

(cid:9)b=

(cid:3)(cid:136)=

(cid:3)kF

(cid:9)G$

(cid:3)o(cid:8)

(cid:9)(cid:10)"

(cid:8)](cid:11)

(cid:9);=

(cid:9)i(cid:4)

(cid:3)C(cid:4)

(cid:9)f>

(cid:9)q[

(cid:3)(cid:130)(cid:8)

(cid:9)D"

(cid:3)m"

(cid:9)w=

(cid:9){#

(cid:3)-"

(cid:9)Z"

(cid:9)u$

(cid:3)o(cid:8)

(cid:9)(cid:10)(cid:11)

(cid:8)A>

(cid:9)(cid:25)=

(cid:3)S(cid:4)

(cid:3)Ir

(cid:9)J"

(cid:9)|$

(cid:3)o(cid:8)

(cid:9)~"

(cid:0)]>

(cid:9)Q>

(cid:8)(cid:22)(cid:4)

(cid:8)(cid:22)#

(cid:9)~R

(cid:9)(cid:131)M

(cid:3)Q(cid:8)

(cid:9)Z"

(cid:0)f(cid:11)

(cid:0);=

(cid:9)i(cid:4)

(cid:3)]#

(cid:9)~R

(cid:2)(cid:131)M

(cid:3)Q(cid:8)

(cid:9)Z"

,](cid:29)

(cid:2);=

(cid:3)a}

(cid:9)~"

(cid:0)(cid:22)>

(cid:0)Q[

(cid:3)(cid:130)(cid:8)

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1.

(cid:9)b"

(cid:9)Ǳ"

(cid:9)1F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)m"

(cid:9)o=

(cid:9)c#

(cid:9)ǱR

(cid:9)_F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)kR

(cid:9)zR

(cid:9)c#

(cid:9)1=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)b.

(cid:9)b(cid:8)

(cid:9)Ir

(cid:9)J(cid:11)

(cid:9)s(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:10)r

(cid:9)(cid:128)(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)q(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:10)r

(cid:9)(cid:128)(cid:5)

(cid:9)|(cid:4)

(cid:9)(cid:18)r

(cid:9)J(cid:11)

(cid:9)(cid:25)(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)~"

Y-(cid:26)

(cid:3)L(cid:29)

(cid:9)J"

(cid:3)(cid:128)"

(cid:9)1"

(cid:7)uM

(cid:3);(cid:8)

(cid:9)!"

(cid:3)!"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)u(cid:26)

(cid:3)<(cid:8)

(cid:9)(cid:10)"

(cid:8)v"

(cid:3)Q>

(cid:3)w#

(cid:3)-"

(cid:3)Z(cid:29)

,w(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)GF

(cid:3)a(cid:29)

(cid:3)b=

(cid:3)G>

(cid:3)C=

(cid:8)k=

(cid:9)z(cid:26)

(cid:3)^(cid:8)

(cid:9)d=

(cid:8)(cid:136)=

(cid:9)i=

(cid:9)?(cid:26)

(cid:3)A"

(cid:9)](cid:29)

(cid:9)u(cid:20)

(cid:3)(cid:130)(cid:8)

(cid:9)D"

(cid:3)](cid:5)

(cid:9)u=

(cid:9)G(cid:26)

(cid:3)^#

(cid:9)-F

(cid:9)i(cid:26)

(cid:3)<(cid:8)

(cid:9)?r

(cid:8)(cid:128)"

(cid:9)(cid:25)=

(cid:3){#

(cid:3)m(cid:4)

(cid:3)I(cid:29)

(cid:9)J(cid:26)

(cid:3)A(cid:8)

(k)
02222220
24222242
13112132
23233231
22122221
22222222
24333342
02111220

(cid:9)?>

(cid:8)^(cid:5)

(cid:3)|(cid:4)

(cid:9)Cr

(cid:9)|(cid:4)

(cid:9)(cid:22)=

(cid:9)i(cid:26)

(cid:3)^(cid:8)

(cid:9)D(cid:26)

(cid:3)A(cid:28)

(cid:9)m#

(cid:3)-"

(cid:9)D(cid:4)

(cid:3)(cid:133)R

(cid:9)GT

(cid:3)b(cid:8)

(cid:9)G(cid:26)

(cid:3)A=

(cid:9)G(cid:4)

(cid:8)f>

(cid:9)g(cid:23)

(cid:8)AF

(cid:9)G(cid:26)

(cid:3)L(cid:8)

(cid:9)?(cid:26)

(cid:3)^=

(cid:9)k(cid:26)

(cid:3)(cid:25)"

(cid:9)J"

(cid:3)o>

(cid:9)u(cid:26)

(cid:3)^(cid:8)

(l)
01200210
16533561
25022052
03200230
02200330
25122141
26442471
01100220

(cid:9)ZR

(cid:0)a.

(cid:9)b=

(cid:9)a=

(cid:3)z=

(cid:9)_R

(cid:9)zM

(cid:3)Q(cid:8)

(cid:9)E"

(cid:9)f(cid:11)

(cid:9)Q=

(cid:9)(cid:131)(cid:4)

(cid:9)]#

(cid:9)Z=

(cid:9)i(cid:20)

(cid:9)j(cid:8)

(cid:9)!"

(cid:9)-"

(cid:9)<(cid:5)

(cid:9)u#

(cid:9)v"

(cid:9)~"

(cid:9);(cid:26)

(cid:9)L(cid:8)

(cid:9)(cid:10)(cid:29)

(cid:8)(cid:128)(cid:5)

(cid:3)|>

(cid:9)(cid:128)#

(cid:3)v(cid:4)

(cid:9)I"

(cid:9)J(cid:20)

(cid:3);(cid:8)

(cid:9)Z>

Y](cid:4)

(cid:8)g=

(cid:9)z=

(cid:9)a>

(cid:9)(cid:22)R

(cid:8)iM

(cid:3)Q(cid:8)

(cid:9)d#

(cid:8)ǱU

(cid:9)(cid:22)(cid:29)

(cid:8)j=

(cid:8)d(cid:4)

(cid:8)(cid:22)=

(cid:9)(cid:131)M

(cid:3)j(cid:8)

(cid:9)kF

(cid:7)z>

P;=

(cid:3)i(cid:4)

(cid:3)f}

(cid:9)~F

(cid:0)(cid:131)M

(cid:3)Q(cid:8)

(cid:9)kF

(cid:9)z"

(cid:9)o"

(cid:9)1#

(cid:9)n=

(cid:9)_F

(cid:9)a.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)m=

(cid:9)cR

(cid:9)_#

(cid:9)1"

(cid:9)mF

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)k#

(cid:9)m=

(cid:9)a=

(cid:9)z#

(cid:9)ǱR

(cid:9)_"

(cid:9)o.

(cid:9)b(cid:8)

Fig. A–20. Record-breaking tarnish counts of closed 8

8 tours.

×

The minimum number of tarnish counts equal to t = (0, 1, . . . , 7) is respectively
(4, 0, 7, 0, 0, 0, 0, 0); and Fig. A–20 shows that each of those minima does occur. Such
examples aren’t very interesting except when t = 0 (that is, when all but the corners
are tarnished) or t = 2 (because the lower bound 7 is a surprise). When t > 2 they’re
not at all rare, having respectively (40666596356, 80536, 960, 40696972, 26645983660,
523634871024, 4873809930916, 11539340580216) exemplars.

160. George Jelliss, in Chessics 2, 19 (Autumn 1984), 25–26, exhibited a tour in which
10 moves are unintersected. He also showed that some move must be intersected at least
four times. When the author asked him in 1992 about the fewest total intersections, he
responded with a tour that has only 76 — but said that such a problem was deﬁnitely
“a task for [your] computers.” Our computers are now ready for this challenge.

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
(cid:19)
$
%
&
(cid:6)
N
(cid:14)
(
)
W
\
(cid:24)
>
(cid:26)
.
&
(cid:13)
t
V
0
(cid:0)
(cid:7)
(cid:3)
U
$
.
3
N
8
(cid:31)

*
P
(cid:7)
(cid:29)
(cid:5)
(cid:19)
$
%
(cid:30)
N
(cid:14)

W
9
(cid:24)
Y
#
(cid:4)
%
&
(
)
\
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
(cid:19)
.
&
H
(cid:14)
t
V

(cid:16)
0
(cid:24)
(cid:2)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
2
(cid:11)
(cid:19)
@
3
(cid:14)
K
4
(cid:16)
X
(cid:2)
(cid:8)
[
T
N
(cid:21)
8
W
9
(cid:24)
,
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
@
V
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
.
N
8
(cid:15)
*
5
P
(cid:0)
>
(cid:29)
(cid:19)
(cid:20)
3
(cid:21)
K

(cid:16)
(cid:24)
(cid:2)
(cid:8)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
#
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
&
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
(cid:11)
(cid:19)
.
@
(cid:14)
8
)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
‘
(cid:14)
(
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
(cid:19)
(cid:20)
(cid:21)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:23)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
r
.
&
(cid:6)
/
)
(cid:15)
0
5
(cid:2)
(cid:7)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:5)
(cid:19)
&
(cid:6)
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:2)
(cid:11)
(cid:23)
.
(cid:13)
(cid:14)
8
)
(cid:15)
(cid:16)
X
(cid:0)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:23)
$
%
(cid:129)
(cid:14)
)
e
9
(cid:24)
,
(cid:0)
(cid:4)
.
&
/
(cid:31)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:12)
$
(cid:6)
’
(cid:14)
W
(cid:24)
P
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
2
3
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
$
T
&
(cid:6)
N
(cid:14)
/
)
e
\
(cid:24)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
.
3
x
8
4
(cid:16)
X
(cid:2)
>
(cid:29)
(cid:20)
%
@
3
O
V

9
:
(cid:2)
(cid:8)
(cid:4)
$
7
N
8
(cid:31)
*
9
Y
(cid:0)
(cid:7)
(cid:4)
(cid:11)
(cid:19)
$
N
(cid:14)
(cid:15)
W
X
P
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
@
3
x
V
4
(cid:16)
X
(cid:2)
(cid:8)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:29)
r
(cid:19)
$
H
N
(cid:14)
V
h
W
X
P
[
T
&
N
O
/
)
*
\
,
(cid:0)
}
(cid:29)
.
3
8
K

(cid:2)
(cid:7)
(cid:3)
$
7
&
(cid:129)
t
*
+
Y
(cid:0)
(cid:7)
#
U
(cid:11)
3
)
h
5
(cid:2)
(cid:7)
(cid:8)
>
(cid:29)
(cid:19)
(cid:20)
T
&
3
x
/
V

(cid:16)
\
(cid:24)
:
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
$
‘
N
(
K
*
0
P
(cid:0)
(cid:7)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:29)
(cid:5)
(cid:30)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
@
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:4)
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
@
N
(cid:14)
(cid:15)
W
X
P
(cid:0)
(cid:20)
@
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
$
’
(cid:14)
(cid:15)
W
(cid:17)
P
(cid:0)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
>
r
(cid:19)
(cid:6)
(cid:14)
K
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
.
N
O
8
*
P
(cid:0)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
$
‘
(cid:6)
N
(
)
(cid:15)
*
0
5
P
(cid:20)
.
O
8
)
(cid:0)
(cid:2)
(cid:3)
(cid:29)
.
3
8

(cid:2)
(cid:7)
(cid:3)
(cid:26)
%
l
(cid:13)
(
)
\
:
(cid:0)
(cid:7)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:5)
.
&
(cid:6)
t
V
0
(cid:2)
(cid:7)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
‘
’
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
[
(cid:129)
O
*
P
(cid:0)
(cid:8)
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
r
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:31)
(cid:15)
(cid:16)
X
(cid:8)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
l
3
N
(cid:14)
(
4
W
\
X
(cid:20)
%
@
(cid:21)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
U
(cid:11)
3
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
(cid:19)
M
%
N
x
e
9
(cid:24)
Y
(cid:0)
(cid:28)
2
(cid:11)
(cid:19)
3
(cid:14)
V
4
(cid:16)
X
(cid:2)
(cid:8)
>
(cid:19)
[
T
&
N
(cid:21)
/
V
W
\
(cid:24)
,
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:12)
$
%
&
’
(cid:14)
(
V
W
\
(cid:24)
Y
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
#
(cid:26)
&
(cid:13)
(
)
0
(cid:0)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
@
(cid:13)
)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:11)
.
@
3
8
4
5
(cid:2)
(cid:7)
(cid:20)
%
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
p
&
(cid:6)
(
(cid:15)
0
5
(cid:2)
(cid:7)
(cid:29)
(cid:11)
(cid:20)
3
O
h
5
(cid:2)
(cid:8)
>
(cid:29)
(cid:5)
(cid:20)
%
&
H
O
(
V

\
:
(cid:2)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
N
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
&
(cid:6)
(
(cid:31)
0
(cid:2)
(cid:7)
(cid:3)
(cid:26)
$
&
(cid:129)
(
*
0
P
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
@
’
(cid:15)
*
5
P
(cid:0)
(cid:7)
(cid:29)
(cid:5)
(cid:20)
H
O
(cid:31)

(cid:2)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
l
N
(cid:14)
(
(cid:15)
W
\
X
Y
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:20)
(cid:13)
x
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
(cid:12)
$
%
&
H
’
(cid:14)
(
)

W
\
(cid:24)
(cid:29)
(cid:5)
T
H
8
)

9
:
(cid:2)
(cid:7)
(cid:29)
T
3
8
(cid:31)

9
:
(cid:2)
(cid:7)
(cid:5)
$
%
&
(cid:6)
N
(
*
+
,
(cid:7)
#
(cid:4)
(cid:11)
&
(
)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
.
&
3
x
t
V
4
(cid:16)
0
X
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
%
@
K
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
>
(cid:11)
$
.
N
8
(cid:31)
(cid:15)
*
5
P
(cid:0)
[
N
O
*
P
(cid:0)
(cid:8)
@
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
$
&
N
(
(cid:15)
*
0
5
P
(cid:0)
(cid:19)
(cid:20)
&
(cid:21)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
N
(cid:14)
(cid:15)
e
(cid:17)
P
(cid:0)
(cid:19)
(cid:20)
l
(cid:21)
(
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
‘
(cid:14)
(
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
p
(cid:19)
(cid:20)
(cid:6)
(cid:21)
)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
#
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:19)
l
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
r
.
&
(cid:6)
/
)
(cid:15)
0
5
(cid:2)
(cid:7)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
p
&
(cid:6)
(
)
(cid:15)
0
5
(cid:2)
(cid:7)
>
(cid:20)
.
&
O
/
K
0
(cid:0)
(cid:2)
(cid:3)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:23)
(cid:13)
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:20)
.
&
O
/
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
M
(cid:6)
N
O
*
P
(cid:8)
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:26)
$
&
(cid:129)
(
(cid:31)
*
0
P
(cid:0)
(cid:7)
(cid:5)
(cid:23)
$
(cid:30)
(cid:129)
(cid:14)

e
(cid:24)
P
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:11)
(cid:19)
$
%
&
N
(cid:14)
(
)
(cid:15)
W
\
X
Y
(cid:19)
(cid:20)
.
&
x
t
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:20)
@
3
O
(cid:31)
h
5
(cid:2)
(cid:8)
[
%
3
N
O

*
9
,
(cid:8)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
%
@
3
(cid:14)
V
4
(cid:16)
9
X
:
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:23)
(cid:20)
(cid:13)
(cid:21)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:20)
(cid:13)
(cid:21)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
’
(cid:14)
)
W
9
(cid:24)
Y
(cid:0)
(cid:28)
(cid:29)
.
&
3
t
V

0
(cid:2)
(cid:7)
(cid:3)
#
$
T
&
N
/
)
*
\
,
(cid:0)
(cid:7)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
p
&
(cid:30)
(
)
4
0
5
(cid:2)
(cid:7)
(cid:29)
(cid:20)
T
&
3
O
/
)

\
:
(cid:2)
T
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
$
%
@
(cid:129)
(cid:14)
)
e
9
(cid:24)
,
(cid:0)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
&
(
(cid:31)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
r
(cid:19)
$
H
N
(cid:14)
h
W
X
P
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
(cid:30)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
@
(cid:13)
)
9
:
(cid:0)
(cid:7)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
U
r
(cid:19)
H
(cid:14)
(cid:31)
h
(cid:16)
X
(cid:2)
(cid:8)
(cid:23)
M
%
(cid:129)
x
(cid:15)
e
9
X
Y
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
‘
3
(
K

0
(cid:2)
(cid:7)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
$
%
(cid:6)
(cid:129)
(cid:14)
(cid:15)
e
9
X
,
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
}
(cid:29)
&
3
(
K

0
(cid:2)
(cid:7)
(cid:3)
$
7
‘
N
t
)
*
+
Y
(cid:0)
(cid:7)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:26)
%
‘
(cid:13)
(
V
+
:
(cid:0)
(cid:7)
(cid:26)
$
.
’
8
(cid:15)
*
5
P
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
(cid:19)
(cid:30)
(cid:14)
K

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
2
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(cid:11)
(cid:19)
%
3
(cid:14)
4
(cid:16)
9
X
:
(cid:2)
(cid:19)
(cid:20)
%
l
(cid:21)
(
(cid:15)
(cid:16)
\
(cid:17)
:
(cid:0)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
2
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:19)
[
%
N
(cid:21)
(cid:15)
W
9
X
,
(cid:0)
>
(cid:29)
(cid:19)
(cid:20)
3
x
V

(cid:16)
(cid:24)
(cid:2)
(cid:8)
7
@
N
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:8)
(cid:26)
(cid:6)
(cid:13)
(cid:15)
5
(cid:7)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
(cid:12)
$
%
(cid:6)
’
(cid:14)
)
(cid:15)
W
9
(cid:17)
Y
>
(cid:29)
(cid:20)
.
3
O
8
K

(cid:2)
(cid:3)
(cid:28)
(cid:29)
$
T
3
N
8
V

*
9
,
(cid:7)
(cid:29)
$
T
&
3
N
/
(cid:31)

*
\
,
(cid:7)
(cid:4)
$
%
&
N
(
*
+
,
(cid:0)
(cid:7)
(cid:29)
p
(cid:12)
&
(cid:30)
(cid:13)
(cid:14)
(
(cid:31)
4
(cid:16)
0
(cid:17)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:26)
$
%
l
(cid:129)
(
K
*
\
Y
(cid:0)
(cid:7)
$
.
N
8
*
P
(cid:0)
(cid:7)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
@
3
4
5
(cid:2)
(cid:7)
(cid:8)
>
(cid:29)
(cid:20)
%
&
3
O
(
V

+
:
(cid:2)
7
@
N
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
2
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
%
@
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:11)
(cid:19)
@
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:19)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
(cid:13)
)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
.
&
(cid:13)
/
)
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:20)
.
O
8
)
(cid:0)
(cid:2)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
.
&
(cid:6)
/
)
0
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
.
H
8
)

(cid:2)
(cid:7)
(cid:3)
T
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:12)
$
%
3
’
(cid:14)
h
W
9
(cid:17)
Y
(cid:20)
%
&
(cid:6)
O
(
\
:
(cid:2)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
p
(cid:19)
$
(cid:30)
N
(cid:14)
(cid:31)
4
e
(cid:17)
P
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
%
l
N
(
)
(cid:15)
*
\
5
Y
(cid:0)
(cid:29)
(cid:11)
(cid:20)
.
3
O
8
(cid:31)
h
5
(cid:2)
2
(cid:11)
[
%
3
N
O
(cid:31)
4
*
9
5
,
2
(cid:19)
[
%
3
N
(cid:21)
(cid:31)

W
9
(cid:24)
,
(cid:4)
(cid:19)
$
%
N
(cid:14)
e
9
(cid:24)
,
(cid:0)
>
(cid:29)
(cid:19)
l
3
(cid:14)
(
V

(cid:16)
0
(cid:24)
(cid:2)
7
@
N
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:16)
(cid:24)
(cid:2)
(cid:8)
p
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:12)
$
%
&
’
(cid:14)
(
)
(cid:15)
W
\
(cid:17)
Y
(cid:20)
.
&
O
t
)
0
(cid:0)
(cid:2)
(cid:3)
}
.
8
K
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
t
(cid:31)
*
0
P
(cid:0)
(cid:7)
#
(cid:4)
$
&
N
(
)
*
0
P
(cid:0)
(cid:7)
>
(cid:29)
p
(cid:19)
.
&
(cid:30)
(cid:14)
t
V
4
(cid:16)
0
(cid:17)
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
%
l
(cid:6)
(
)
\
:
(cid:2)
(cid:7)
(cid:26)
.
(cid:13)
8
(cid:15)
5
(cid:0)
(cid:7)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
&
(cid:6)
(
V
0
(cid:2)
(cid:7)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(cid:11)
3
(cid:31)
4
5
(cid:2)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
[
%
&
3
N
(cid:21)
(
4
W
+
X
(cid:19)
(cid:20)
%
3
(cid:21)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:23)
%
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:11)
(cid:26)
(cid:20)
(cid:13)
O
(cid:31)
(cid:15)
5
(cid:0)
(cid:8)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
$
&
N
(
*
0
P
(cid:0)
(cid:7)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
.
3
8
)

(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
7
3
8
)

9
:
(cid:2)
(cid:7)
(cid:28)
(cid:29)
(cid:11)
T
&
3
/
V
h
\
5
:
(cid:2)
T
&
N
O
/
*
\
,
(cid:0)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
$
@
’
(cid:14)
(cid:15)
W
(cid:17)
P
(cid:0)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
p
(cid:19)
@
(cid:30)
(cid:14)
4
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
l
N
(cid:14)
(
)
(cid:15)
W
\
X
Y
(cid:11)
(cid:19)
(cid:20)
.
x
8
(cid:31)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:4)
(cid:11)
[
N
O
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:19)
M
N
x
e
(cid:24)
P
(cid:0)
(cid:4)
(cid:11)
(cid:19)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
&
3
x
(
V
4
(cid:16)
0
X
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
p
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:11)
(cid:12)
$
%
&
3
’
(cid:14)
(
)
h
W
\
(cid:17)
(cid:20)
7
&
O
t
)
+
:
(cid:0)
(cid:2)
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
(cid:26)
$
%
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
}
(cid:4)
&
(
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
p
(cid:19)
$
.
&
(cid:30)
N
(cid:14)
t
V
4
e
0
(cid:17)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
l
(
)
\
:
(cid:0)
(cid:2)
(cid:7)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
>
(cid:29)
(cid:26)
3
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
$
%
@
N
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
>
l
(
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
H
(cid:14)
h
(cid:16)
X
(cid:2)
(cid:8)
(cid:19)
(cid:20)
%
3
x

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:4)
(cid:19)
%
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:19)
@
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
>
(cid:4)
(cid:12)
(cid:13)
(cid:14)
V
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:23)
$
.
(cid:129)
(cid:14)
8
(cid:15)
e
X
P
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
&
(
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:19)
$
.
N
(cid:14)
8
)
W
(cid:24)
P
(cid:5)
.
(cid:6)
8
)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:26)
.
3
(cid:13)
8
)

(cid:7)
(cid:3)
#
(cid:29)
T
3
8
)

9
:
(cid:2)
(cid:7)
7
‘
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
$
(cid:6)
’
(cid:14)
(cid:15)
W
(cid:17)
P
(cid:20)
@
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
(cid:26)
$
%
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
(cid:12)
(cid:30)
(cid:13)
(cid:14)
4
(cid:16)
(cid:17)
(cid:8)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
(cid:11)
(cid:19)
$
%
l
N
(cid:14)
(
K
(cid:15)
W
\
X
Y
(cid:19)
M
.
N
x
8
(cid:15)
e
(cid:17)
P
>
(cid:29)
(cid:20)
3
O
(cid:31)

(cid:2)
(cid:8)
(cid:3)
$
%
@
N
*
9
Y
(cid:0)
(cid:7)
(cid:8)
U
(cid:11)
(cid:19)
3
(cid:14)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
%
&
3
x
(
V
4
(cid:16)
+
X
:
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
l
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:4)
$
&
N
(
V
*
0
P
(cid:0)
(cid:7)
}
(cid:29)
(cid:11)
(cid:19)
$
.
&
3
N
(cid:14)
/
K
4
W
0
X
7
&
N
O
t
*
+
Y
(cid:0)
(cid:5)
(cid:26)
(cid:30)
(cid:13)

(cid:7)
(cid:8)
(cid:3)
#
2
%
3
)

9
:
(cid:2)
(cid:7)
(cid:8)
>
(cid:29)
r
(cid:19)
7
&
H
(cid:14)
t
K
h
(cid:16)
+
X
:
T
N
O
8
*
9
,
(cid:0)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
$
@
N
(cid:14)
e
(cid:24)
P
(cid:0)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
3
8

(cid:2)
(cid:7)
(cid:3)
>
(cid:26)
%
(cid:13)
(cid:31)
9
:
(cid:0)
(cid:7)
(cid:8)
#
$
N
*
P
(cid:0)
(cid:7)
(cid:8)
>
(cid:5)
&
(cid:6)
(
K
0
(cid:2)
(cid:7)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
@
N
(cid:14)
)
(cid:15)
e
(cid:17)
P
(cid:0)
(cid:19)
(cid:20)
.
(cid:21)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
@
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
p
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:31)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
$
l
N
(
)
*
0
P
(cid:0)
(cid:7)
(cid:5)
.
&
(cid:6)
/
)
0
(cid:2)
(cid:7)
(cid:3)
(cid:29)
.
3
8

(cid:2)
(cid:7)
(cid:3)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
#
(cid:4)
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:5)
(cid:19)
.
&
(cid:6)
(cid:14)
/
K
(cid:16)
0
(cid:24)
(cid:2)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
$
@
(cid:129)
(cid:14)
(cid:15)
e
X
P
(cid:0)
(cid:26)
(cid:20)
(cid:13)
O
(cid:31)
(cid:0)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
$
3
’

*
P
(cid:7)
(cid:8)
(cid:5)
%
(cid:6)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
>
(cid:5)
(cid:20)
(cid:6)
O
K
(cid:2)
(cid:8)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
(cid:28)
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
(cid:11)
(cid:19)
$
%
‘
3
N
(cid:14)
(
)
h
e
+
(cid:17)
(cid:19)
(cid:20)
T
3
x
8

(cid:16)
9
(cid:24)
:
%
@
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
U
(cid:11)
3
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
>
(cid:4)
(cid:11)
(cid:19)
M
%
&
N
x
(
V
(cid:15)
e
\
(cid:17)
Y
(cid:11)
(cid:19)
[
.
N
(cid:21)
8
(cid:31)
(cid:15)
W
X
P
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:29)
(cid:12)
$
%
&
3
’
(cid:14)
(
V

W
\
(cid:24)
$
T
&
’
/
*
\
,
(cid:0)
(cid:7)
(cid:5)
(cid:26)
H
(cid:13)

(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:26)
%
(cid:6)
(cid:13)
)
9
:
(cid:7)
(cid:8)
(cid:28)
(cid:29)
.
3
8
V

(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
p
$
T
&
(cid:30)
N
/
V
4
*
\
5
,
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
%
@
3
)

9
:
(cid:2)
(cid:7)
(cid:8)
7
@
3
8

9
:
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
%
H
(cid:31)

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:4)
(cid:26)
$
%
(cid:129)
(cid:31)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:19)
$
N
(cid:14)
e
(cid:24)
P
(cid:0)
>
‘
(
(cid:31)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
(cid:129)
(cid:14)
(cid:15)
e
X
P
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:4)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
.
H
(cid:14)
8
h
(cid:16)
X
(cid:2)
%
@
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:9)
(cid:7)
#
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
%
‘
(
)
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:19)
.
(cid:6)
(cid:14)
8
(cid:16)
(cid:24)
(cid:2)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
>
(cid:20)
&
O
(
K
0
(cid:0)
(cid:2)
(cid:3)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
(cid:6)
’
(cid:15)
*
5
P
(cid:7)
>
(cid:26)
(cid:20)
(cid:13)
O
K
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
$
.
3
N
8
(cid:31)

*
P
(cid:7)
(cid:29)
$
%
@
3
N

*
9
Y
(cid:7)
(cid:8)
(cid:5)
%
&
(cid:6)
(
+
:
(cid:2)
(cid:7)
(cid:5)
(cid:23)
(cid:30)
(cid:13)
(cid:14)

(cid:16)
(cid:24)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(cid:11)
(cid:19)
$
%
l
3
N
(cid:14)
(
(cid:31)
4
W
\
X
(cid:19)
[
%
N
(cid:21)
W
9
(cid:24)
,
(cid:0)
(cid:19)
@
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
@
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
2
(cid:11)
(cid:20)
3
O
(cid:31)
4
5
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
[
%
3
N
(cid:21)
V
4
W
9
X
,
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
$
%
&
(cid:6)
N
(
)
*
\
Y
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
@
’
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
[
(cid:6)
N
O
*
P
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:19)
(cid:20)
3
x
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
(cid:129)
(
*
\
Y
(cid:0)
(cid:7)
(cid:29)
@
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
&
’
(
*
+
,
(cid:0)
(cid:7)
(cid:28)
(cid:5)
&
(cid:6)
(
V
0
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
%
@
(cid:15)
9
5
:
(cid:0)
(cid:2)
(cid:7)
(cid:4)
(cid:19)
(cid:20)
(cid:21)
(cid:31)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
$
@
(cid:129)
(cid:14)
e
(cid:24)
P
(cid:0)
>
(cid:5)
(cid:6)
K
(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:28)
(cid:11)
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
M
&
’
O
(
*
0
P
(cid:0)
(cid:29)
(cid:5)
(cid:26)
H
(cid:13)
)

(cid:7)
(cid:8)
(cid:3)
T
@
8
)
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:20)
&
3
O
(
h
0
5
(cid:2)
(cid:19)
(cid:20)
%
@
3
x

(cid:16)
9
(cid:24)
:
(cid:2)
>
(cid:4)
(cid:11)
%
(cid:31)
(cid:15)
9
5
:
(cid:0)
(cid:2)
(cid:7)
(cid:11)
(cid:19)
[
N
(cid:21)
(cid:15)
W
X
P
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:29)
(cid:11)
(cid:12)
$
3
’
(cid:14)
V
h
W
(cid:17)
P
>
[
T
&
N
O
/
V
*
\
,
(cid:0)
(cid:29)
(cid:5)
$
.
H
N
8
(cid:31)

*
P
(cid:7)
(cid:29)
(cid:26)
$
%
3
(cid:129)

*
9
Y
(cid:7)
(cid:8)
(cid:28)
2
%
&
3
(
V

\
:
(cid:2)
(cid:7)
p
(cid:19)
$
T
&
(cid:30)
N
(cid:14)
/
4
e
\
(cid:17)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
$
%
l
N
(cid:14)
(
)
W
\
(cid:24)
Y
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
@
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
N
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
l
3
(
V
4
0
5
(cid:2)
(cid:7)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
@
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
.
x
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
&
(cid:13)
(
)
0
(cid:0)
(cid:7)
(cid:3)
(cid:26)
.
&
(cid:13)
t
)
0
(cid:0)
(cid:7)
(cid:3)
.
(cid:6)
8
(cid:2)
(cid:7)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:11)
&
(
)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:19)
(cid:20)
.
&
x
t
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:23)
$
%
H
(cid:129)
(cid:14)
h
e
9
X
,
(cid:20)
%
(cid:6)
O
9
:
(cid:2)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
H
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
&
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
(cid:29)
r
(cid:23)
H
(cid:13)
(cid:14)
)
h
(cid:16)
X
(cid:8)
7
O
8
9
:
(cid:0)
(cid:2)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
$
%
‘
N
(
K
(cid:15)
*
+
5
,
(cid:0)
(cid:29)
(cid:11)
M
.
3
N
O
8
(cid:31)
h
*
5
>
(cid:29)
[
%
3
N
O
(cid:31)

*
9
,
(cid:8)
$
%
@
N
*
9
Y
(cid:0)
(cid:7)
(cid:8)
U
(cid:11)
(cid:19)
3
(cid:14)
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:11)
(cid:19)
M
%
&
N
x
(
K
(cid:15)
e
\
(cid:17)
Y
.
N
O
8
*
P
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
l
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
88

ANSWERS TO EXERCISES

7.2.2.4

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:5)

(cid:9)q(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)r

(cid:9)q(cid:4)

(cid:9)gr

(cid:9)(cid:128)(cid:4)

(cid:9)(cid:22)r

(cid:9)(cid:128)(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:12)

(cid:9)s(cid:4)

(cid:9)I(cid:12)

(cid:9)s(cid:4)

(cid:9)Ir

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)!"

(cid:3)(cid:128)"

(cid:9)n#

(cid:3)1"

(cid:9)v"

(cid:9)n"

(cid:9)QM

(cid:3);(cid:8)

(cid:9)Z"

(cid:0)v"

(cid:9)L#

(cid:3)1"

(cid:3)(cid:128)#

(cid:7)n"

(cid:3)s(cid:26)

(cid:3)<(cid:8)

(cid:9)D"

(cid:3)(cid:128)"

(cid:3)n>

(cid:9)L"

(cid:3)D(cid:28)

(cid:9)n"

(cid:3)q(cid:26)

(cid:3)L(cid:8)

(cid:9)?>

(cid:3)^=

(cid:3)G(cid:29)

(cid:9)(cid:134)#

(cid:3)Z#

(cid:9)~=

(cid:9)(cid:131)(cid:20)

(cid:9)(cid:130)(cid:8)

(cid:9)d"

(cid:8)^(cid:20)

(cid:3)Q=

(cid:9)a}

(cid:3)v=

(cid:7)a=

(cid:3)(cid:131)(cid:26)

(cid:3)^(cid:8)

(cid:9)G=

(cid:8)a(cid:29)

(cid:3)|=

(cid:3)?(cid:28)

(cid:9)Ǳ(cid:4)

(cid:3)g=

(cid:9)a(cid:26)

(cid:3)A(cid:8)

bitwise trick
trick
Stappers

(cid:9)?(cid:26)

(cid:3)A>

(cid:9)(cid:134)=

(cid:3)G#

(cid:3)Z"

(cid:9)Z"

(cid:9)Q(cid:20)

(cid:9);(cid:8)

(cid:9)_F

(cid:7)(cid:136)(cid:11)

(cid:9)Q=

(cid:9)(cid:131)#

(cid:3)-=

(cid:9)a=

(cid:9)i(cid:26)

(cid:3)s(cid:8)

(cid:9)k(cid:26)

(cid:3)^=

(cid:9)a(cid:28)

(cid:8)Dp

Pq(cid:20)

(cid:9)jR

(cid:9)?T

(cid:3)o(cid:8)

(a)

(cid:9)G(cid:26)

(cid:3)A>

(cid:9)(cid:128)>

(cid:3)]#

(cid:8)Ǳ"

(cid:9)~"

(cid:9)u(cid:20)

(cid:9)Q(cid:8)

(b)

(cid:9)_#

(cid:3)-r

(cid:9)J=

(cid:9)i#

(cid:3)v#

(cid:9)~=

(cid:9)S(cid:26)

(cid:3)s(cid:8)

(c)

(cid:9)(cid:10)(cid:12)

(cid:8)^#

(cid:9)!}

(cid:9)m>

(cid:3)(cid:130)(cid:5)

(cid:3)J=

(cid:9)?(cid:26)

(cid:3)(cid:25)(cid:8)

(cid:9)?(cid:29)

(cid:3)A>

(cid:3)J(cid:26)

(cid:3)^"

(cid:9)]#

(cid:9)1"

(cid:9)q(cid:26)

(cid:3)<(cid:8)

(cid:9)?#

(cid:3)v>

(cid:7)J=

(cid:3)(cid:131)(cid:5)

(cid:3)J#

(cid:9)~F

(cid:2)?(cid:26)

(cid:3)<(cid:8)

(cid:9)G"

(cid:3)J}

(cid:9)1(cid:5)

(cid:3)|(cid:29)

(cid:9)^(cid:28)

(cid:3)Ǳ>

(cid:3)J(cid:26)

(cid:3)A(cid:8)

(cid:9)d=

(cid:8)a>

(cid:3)g(cid:4)

(cid:8)]#

(cid:9)Z"

(cid:9)g>

(cid:9);M

(cid:3)(cid:130)(cid:8)

(cid:9)d=

(cid:8)_>

(cid:3)(cid:22)=

(cid:8)z>

(cid:3)g=

(cid:8)ER

(cid:9)(cid:131)M

(cid:3);(cid:8)

(cid:9)E}

(cid:8)m(cid:4)

(cid:0)(cid:22)>

(cid:9)(cid:130)=

(cid:8)E2

(cid:9)(cid:22)=

(cid:8)zM

(cid:3)(cid:130)(cid:8)

(cid:9)kF

(cid:9)z=

(cid:9)c"

(cid:9)m"

(cid:9)n"

(cid:9)1F

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)_F

(cid:9)z#

(cid:9)nF

(cid:9)z#

(cid:9)1"

(cid:9)mF

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)Ǳ.

(cid:9)bR

(cid:9)_.

(cid:9)bR

(cid:9)_F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)C(cid:4)

(cid:9)Cp

(cid:9)J(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)(cid:5)

(cid:9)q(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:22)r

(cid:9)J(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)!"

(cid:7)D"

(cid:0)Q"

(cid:9)Q"

(cid:3)6"

(cid:2)n"

(cid:3)u(cid:26)

(cid:3)L(cid:8)

(cid:9)Z"

(cid:0)v"

(cid:9)n"

(cid:9)n"

(cid:9)1"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)Z"

Y!"

(cid:9)L"

(cid:9)1(cid:11)

(cid:7)<"

(cid:9)(cid:138)"

(cid:3)Q(cid:26)

(cid:3)<(cid:8)

(cid:9)!}

(cid:7)Ǳ[

(cid:3)j=

(cid:9)G=

(cid:9)GF

(cid:9)E=

(cid:9){(cid:26)

(cid:3)A(cid:8)

(cid:9)G"

(cid:8)](cid:19)

(cid:9)Q(cid:4)

(cid:9)(cid:18)(cid:12)

(cid:9)s(cid:4)

(cid:9)(cid:18)=

(cid:9)(cid:131)(cid:26)

(cid:3)^(cid:8)

(cid:9)?"

(cid:9)^[

(cid:3)Q=

(cid:9)_#

(cid:3)Ǳ=

(cid:9)S=

(cid:9)i(cid:26)

(cid:3)A(cid:8)

(cid:9)Dr

(cid:7)(cid:135)(cid:11)

(cid:9)j>

(cid:9)|>

(cid:8)q(cid:4)

(cid:8)gF

(cid:9)(cid:131)7

(cid:3)b(cid:8)

(cid:9)_(cid:5)

(cid:3)(cid:128)"

(cid:9)D(cid:29)

(cid:3)w"

(cid:3)!(cid:4)

(cid:3)6R

(cid:9)?T

(cid:3)b(cid:8)

(cid:9)Z=

(cid:0)(cid:136)(cid:11)

(cid:9)(cid:130)=

(cid:9)i#

(cid:9)v(cid:4)

(cid:3)g=

(cid:9)G(cid:26)

(cid:3)(cid:25)(cid:8)

(d)

(cid:9)D}

(cid:7)m#

(cid:3)(cid:138)(cid:28)

(cid:9)D}

(cid:7)Ǳ[

(cid:3)jF

(cid:9)?(cid:26)

(cid:9)L(cid:8)

(e)

(cid:9)I>

(cid:8)^=

(cid:8)d=

(cid:8)(cid:131)=

(cid:8)d(cid:4)

(cid:8)(cid:22)F

(cid:9)G(cid:26)

(cid:3)<(cid:8)

(f)

(cid:9)_"

(cid:3)m(cid:11)

(cid:9)L#

(cid:9)(cid:137)=

(cid:3)S#

(cid:9)!R

(cid:9)(cid:136)M

(cid:3)Q(cid:8)

(cid:9)!(cid:11)

(cid:7)^(cid:20)

(cid:9)(cid:130)(cid:28)

(cid:9)v(cid:26)

(cid:3)A(cid:4)

(cid:9)]>

(cid:9)J(cid:26)

(cid:3)s(cid:8)

(cid:9)?"

(cid:3)-.

(cid:9)o"

(cid:9)Ǳ.

(cid:9)o"

(cid:9)(cid:135)"

(cid:9)u$

(cid:3)b(cid:8)

(cid:9)?#

(cid:9)v(cid:26)

(cid:3)(cid:25)=

(cid:9)G(cid:26)

(cid:3)(cid:25)(cid:28)

(cid:9)Z=

,G(cid:26)

(cid:9)^(cid:8)

(cid:9)Z(cid:4)

(cid:0)]U

(cid:9)(cid:22)2

(cid:8)g(cid:4)

(cid:8)]#

(cid:9)~R

(cid:2)(cid:131)$

(cid:3)b(cid:8)

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)>

(cid:9)(cid:22)=

(cid:8)iM

(cid:3)j(cid:8)

(cid:9)Z=

Yd#

(cid:8)(cid:138)=

(cid:9)E(cid:4)

(cid:8)g=

(cid:9)d"

(cid:9)(cid:130)M

(cid:3)Q(cid:8)

(cid:9)_"

(cid:9)mR

(cid:9)cR

(cid:9){"

(cid:9)1R

(cid:9)cR

(cid:9){.

(cid:9)b(cid:8)

(cid:9)k"

(cid:9)m"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)n"

(cid:9)b.

(cid:9)b(cid:8)

(cid:9)_F

(cid:9)z"

(cid:9)n=

(cid:9)c"

(cid:9)Ǳ"

(cid:9)1F

(cid:9)c.

(cid:9)o(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)g(cid:4)

(cid:9)C(cid:4)

(cid:9)Cp

(cid:9)J(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:5)

(cid:9)|(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)gr

(cid:9)J(cid:26)

(cid:9)s(cid:8)

(cid:9)(cid:10)"

(cid:8)D"

(cid:3)u"

(cid:9)w"

(cid:3)w"

(cid:3)n"

(cid:7)u[

(cid:3)Q(cid:8)

(cid:9)Z"

(cid:0)v"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)QM

(cid:3);(cid:8)

(cid:9)I"

(cid:8)v"

(cid:3)u"

(cid:9)n(cid:4)

(cid:3)6"

(cid:9)D"

(cid:7)wM

(cid:3)Q(cid:8)

(cid:9)?R

(cid:8)a>

(cid:3);=

(cid:3)G=

(cid:3)E=

(cid:8)_=

(cid:9)?[

(cid:3)(cid:130)(cid:8)

(cid:9)d"

(cid:8)^(cid:11)

(cid:9)Q(cid:5)

(cid:9)|#

(cid:9)Z#

(cid:9)~=

(cid:9)(cid:131)(cid:20)

(cid:9)j(cid:8)

(cid:9)IF

(cid:8)a>

(cid:9)o=

(cid:3)?(cid:26)

(cid:9)AF

(cid:9)_=

(cid:3){(cid:26)

(cid:3)A(cid:8)

(cid:9)D(cid:4)

(cid:7)f(cid:19)

(cid:9)j>

(cid:9)(cid:135)(cid:4)

(cid:3)]"

(cid:9)Ǳ>

(cid:9)w[

(cid:3)(cid:130)(cid:8)

(cid:9)_"

(cid:7)v(cid:11)

(cid:9)Q>

(cid:9)g#

(cid:8)Z"

(cid:9)~"

(cid:9)u(cid:20)

(cid:9);(cid:8)

(cid:9)E"

(cid:8)^(cid:20)

(cid:9)Q>

(cid:9)f(cid:4)

(cid:8)(cid:22)(cid:4)

(cid:9)I(cid:29)

(cid:9)(cid:134)(cid:20)

(cid:3)j(cid:8)

(g)

(cid:9)D(cid:4)

(cid:7)f"

(cid:9)|>

(cid:9)u(cid:5)

(cid:3)(cid:134)"

(cid:9)!>

(cid:9)w[

(cid:3)(cid:130)(cid:8)

(h)

(cid:9)_#

(cid:7)v(cid:11)

(cid:9)(cid:25)(cid:4)

(cid:9)g"

(cid:9)f"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)<(cid:8)

(i)

(cid:9)!"

(cid:3)^#

(cid:9)1=

(cid:9)?"

(cid:9)(cid:135)"

(cid:9)nF

(cid:3){(cid:26)

(cid:3)L(cid:8)

(cid:9)D(cid:11)

(cid:7)^"

(cid:9)s>

(cid:3)L>

(cid:3)A(cid:28)

(cid:3)Z>

PJ(cid:26)

(cid:3)^(cid:8)

(cid:9)_#

(cid:7)v(cid:11)

(cid:0)(cid:25)(cid:11)

(cid:9)(cid:25)"

(cid:9)(cid:25)"

(cid:9)L>

(cid:9)u(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:4)

(cid:3)Cp

(cid:9)(cid:128)>

(cid:9)|>

(cid:3)(cid:18)(cid:4)

(cid:8)(cid:10)(cid:29)

(cid:9)(cid:134)(cid:26)

(cid:3)^(cid:8)

(cid:9)~U

,]2

(cid:8)(cid:22)2

(cid:8)f(cid:4)

(cid:8)fU

(cid:9)]"

(cid:8)(cid:130)$

(cid:3)o(cid:8)

(cid:9)_=

(cid:7)_#

(cid:2)(cid:138)2

(cid:2)(cid:22)U

(cid:8)(cid:22)(cid:4)

(cid:8)(cid:22)=

(cid:9)iM

(cid:3)(cid:130)(cid:8)

(cid:9)E#

(cid:8)m"

(cid:3)(cid:22)>

P(cid:133)(cid:19)

(cid:8)(cid:130)"

(cid:9)fR

P{M

(cid:3);(cid:8)

(cid:9)_R

(cid:9)aR

(cid:9){R

(cid:9){"

(cid:9)1R

(cid:9)cR

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)_=

(cid:9)_=

(cid:9)_=

(cid:9)_R

(cid:9)k"

(cid:9)1F

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_F

(cid:9)a#

(cid:9)1F

(cid:9)a"

(cid:9)b#

(cid:9)nF

(cid:9)z.

(cid:9)o(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)gr

(cid:9)J(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)(cid:128)(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)I(cid:4)

(cid:9)(cid:18)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)r

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)!"

(cid:3)v"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)<(cid:8)

(cid:9)D"

(cid:3)(cid:18)"

(cid:9)n"

(cid:3)1(cid:26)

(cid:3)L"

(cid:9)Z"

:L(cid:26)

(cid:3)<(cid:8)

(cid:9)Z"

(cid:0)v"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)<(cid:8)

(cid:9)dr

(cid:8)(cid:134)(cid:26)

(cid:9)(cid:25)(cid:4)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)(cid:22)=

(cid:9)(cid:131)M

(cid:3)j(cid:8)

(cid:9)d(cid:11)

(cid:8)^R

(cid:9)i2

(cid:9)6(cid:12)

(cid:8)A=

(cid:9)?R

(cid:3)iT

(cid:3)o(cid:8)

(cid:9)d"

(cid:8)^r

(cid:9)u(cid:5)

(cid:9)|(cid:4)

(cid:9)I(cid:4)

(cid:9)(cid:22)=

(cid:9)(cid:131)M

(cid:3)j(cid:8)

(cid:9)_"

(cid:9)f(cid:11)

(cid:0)Q}

(cid:9)(cid:138)"

(cid:3)Z"

(cid:9)nF

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)k"

(cid:7)(cid:134)(cid:11)

(cid:9)Q=

(cid:9)(cid:131)"

(cid:3)v=

(cid:9){=

(cid:8)i(cid:26)

(cid:9)s(cid:8)

(cid:9)G"

(cid:8)D>

(cid:9)Q(cid:28)

(cid:3)-(cid:28)

(cid:3)-"

(cid:3)vF

(cid:9)c.

(cid:9)b(cid:8)

(j)

(cid:9)Z=

(cid:9)_"

(cid:9)j=

(cid:9)c(cid:5)

(cid:9)(cid:134)"

(cid:9)Cr

(cid:9)u(cid:26)

(cid:9)s(cid:8)

(k)

(cid:9)_}

(cid:9)-(cid:4)

(cid:7)C=

(cid:9)(cid:131)#

(cid:3)v#

(cid:9)~(cid:29)

(cid:9)(cid:135)(cid:26)

(cid:3)(cid:25)(cid:8)

(l)

(cid:9)_>

(cid:7)(cid:18)(cid:29)

(cid:8)(cid:25)2

(cid:3)f2

(cid:8)f(cid:4)

(cid:8)]r

(cid:9)q(cid:26)

(cid:9)s(cid:8)

(cid:9)D"

(cid:9)C(cid:11)

(cid:9)Q(cid:5)

(cid:9)|>

(cid:9)(cid:18)#

(cid:8)D"

(cid:9)J(cid:26)

(cid:3)L(cid:8)

(cid:9)(cid:10)#

(cid:8)-(cid:26)

(cid:3)^R

(cid:9)G(cid:4)

(cid:3)(cid:133)#

(cid:9)-R

(cid:9)?(cid:26)

(cid:3)<(cid:8)

(cid:9)!(cid:29)

(cid:3)^F

(cid:3)a=

(cid:9){R

(cid:9)_"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)<(cid:8)

(cid:9)Z#

(cid:0)~"

(cid:9)(cid:22)>

(cid:9)Q=

(cid:3)i"

(cid:9)]=

Y{M

(cid:3)(cid:130)(cid:8)

(cid:9)dF

(cid:8)E(cid:19)

(cid:2);=

(cid:9)E2

(cid:8)g"

(cid:8)(cid:22)=

(cid:9)cM

(cid:3)(cid:130)(cid:8)

(cid:9)d=

(cid:8)E(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)=

(cid:9)(cid:131)M

(cid:3)j(cid:8)

(cid:9)_"

(cid:9)Ǳ"

(cid:9)nF

(cid:9){.

(cid:9)b=

(cid:9)_F

(cid:9)a.

(cid:9)b(cid:8)

(cid:9)kF

(cid:9)z"

(cid:9)n#

(cid:9)1F

(cid:9)a"

(cid:9)1F

(cid:9)c.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)m"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)nF

(cid:9)c.

(cid:9)b(cid:8)

Fig. A–21. Record-breaking intersection statistics of closed 8

8 tours.

×

Every knight move can be intersected by at most nine others, and by at most
seven others in any given tour. (See FGbook page 497.) To speed up the census, we
64
want a fast way to discover all of a tour’s self-intersections. The obvious way does
2
table-lookups; but there’s a nice bitwise trick that needs only 64: The edges of any
(cid:16)
given tour can be represented in four 64-bit words called NW, NE, SW, SE, where each
of those words has 16 bits from each of the four diagrams in exercise 157. (Edges of
class U appear in all four of those words; edges of classes
appear
in two of them.) Given an edge u
v, we can assume that v is not one of the four
central cells. Then if v is in the upper right quadrant, say, the number of edges that
cross u

v is ν(NE & mv), for some 64-bit mask mv with ν(mv)

C, D, I, J, O, P, S, T

−−−

9.

{

}

(cid:15)

A census conducted by Filip Stappers has uncovered many surprising facts about
intersections. For example, there’s an essentially unique cycle that achieves 16(!) un-

−−−

≤

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:26)
$
%
&
(cid:6)
(cid:129)
(
)
*
\
Y
(cid:7)
}
(cid:29)
.
3
8
K

(cid:2)
(cid:7)
(cid:3)
$
7
&
N
t
*
+
Y
(cid:0)
(cid:7)
#
(cid:26)
&
(cid:13)
(
)
0
(cid:0)
(cid:7)
(cid:3)
#
(cid:11)
.
&
t
)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:11)
(cid:20)
.
&
3
O
t
V
4
0
5
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
(cid:129)
(cid:31)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
$
(cid:6)
N
*
P
(cid:7)
(cid:8)
(cid:5)
@
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
%
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
@
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
$
(cid:6)
N
(cid:31)
*
P
(cid:7)
(cid:8)
(cid:4)
$
N
*
P
(cid:0)
(cid:7)
(cid:8)
#
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
.
&
x
t
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:26)
(cid:6)
(cid:13)
(cid:31)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
$
@
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:19)
$
@
N
(cid:14)
W
(cid:24)
P
(cid:0)
#
(cid:4)
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
p
(cid:19)
.
&
(cid:6)
(cid:14)
t
)
(cid:15)
(cid:16)
0
(cid:17)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
3
(cid:129)

*
9
Y
(cid:7)
(cid:8)
(cid:5)
(cid:26)
%
(cid:6)
(cid:13)
(cid:31)
9
:
(cid:7)
(cid:8)
$
@
’
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:4)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
>
(cid:5)
(cid:20)
&
(cid:6)
O
(
K
0
(cid:2)
(cid:3)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
4
W
9
X
Y
2
(cid:20)
%
3
O
(cid:31)

9
:
(cid:2)
(cid:8)
(cid:19)
$
%
@
N
(cid:14)
e
9
(cid:24)
,
(cid:0)
(cid:4)
(cid:11)
(cid:19)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
(cid:20)
&
x
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
.
3
x
8
(cid:31)
4
(cid:16)
X
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
&
’
(cid:14)
(
)
W
\
(cid:24)
Y
>
(cid:26)
.
&
(cid:13)
t
V
0
(cid:0)
(cid:7)
(cid:3)
(cid:29)
$
.
3
N
8

*
P
(cid:7)
>
(cid:5)
(cid:26)
%
&
(cid:6)
(cid:13)
(
V
\
:
(cid:7)
(cid:29)
(cid:11)
$
.
3
N
8
h
*
5
P
>
(cid:29)
(cid:26)
(cid:20)
%
&
3
(cid:13)
O
(
V

\
:
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
U
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:23)
%
@
3
(cid:13)
(cid:14)
)
4
(cid:16)
9
X
:
T
O
8
9
:
(cid:0)
(cid:2)
(cid:29)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
(cid:13)
(cid:31)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:11)
$
‘
3
N
(
h
*
0
5
P
(cid:29)
(cid:20)
%
3
O

9
:
(cid:2)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
%
&
(cid:13)
(
)
(cid:15)
\
5
:
(cid:0)
(cid:20)
.
O
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:11)
‘
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:29)
(cid:11)
(cid:20)
3
O
4
5
(cid:2)
(cid:8)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
&
(cid:13)
(
\
:
(cid:0)
(cid:7)
(cid:26)
&
(cid:6)
(cid:13)
(
(cid:15)
0
5
(cid:7)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:4)
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:11)
(cid:23)
&
3
(cid:13)
(cid:14)
(
4
(cid:16)
0
X
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
3
(cid:13)

9
:
(cid:7)
(cid:8)
r
(cid:26)
%
&
(cid:6)
(cid:13)
(
(cid:31)
(cid:15)
+
5
:
(cid:29)
M
3
N
O

*
P
(cid:8)
(cid:26)
%
(cid:6)
(cid:13)
9
:
(cid:7)
(cid:8)
2
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
%
&
(cid:30)
(cid:14)
(
)

(cid:16)
\
(cid:24)
:
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:11)
(cid:19)
$
%
3
N
(cid:14)
4
W
9
X
Y
(cid:4)
(cid:20)
%
&
O
(
(cid:31)
+
:
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:19)
$
@
3
N
(cid:14)
4
W
X
P
(cid:4)
(cid:20)
%
O
(cid:31)
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
$
N
(cid:14)
(cid:15)
W
X
P
(cid:0)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
V
4
(cid:16)
X
(cid:2)
(cid:8)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:20)
(cid:13)
x
(cid:16)
(cid:24)
(cid:0)
(cid:8)
p
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
(cid:13)
x
(cid:16)
(cid:24)
(cid:0)
(cid:8)
p
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
(cid:26)
$
%
&
H
(cid:129)
(
)

*
\
Y
(cid:7)
#
T
8
)
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:29)
(cid:26)
.
&
3
(cid:13)
t
(cid:31)

0
(cid:7)
(cid:3)
#
(cid:5)
$
%
(cid:6)
N
)
*
9
Y
(cid:7)
(cid:8)
(cid:11)
.
&
t
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
M
&
H
N
O
(
V

*
0
P
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
$
%
@
N
(cid:31)
(cid:15)
*
9
5
Y
(cid:0)
(cid:7)
(cid:5)
[
(cid:30)
N
O

*
P
(cid:8)
(cid:5)
%
(cid:6)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:11)
@
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
M
&
N
O
(
*
0
P
(cid:0)
>
(cid:29)
(cid:19)
@
3
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:28)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
l
(cid:129)
(
*
0
P
(cid:0)
(cid:7)
>
@
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
$
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
M
&
(cid:6)
N
O
(
(cid:15)
*
0
5
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
H
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
2
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
@
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
l
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
[
‘
N
O
(
(cid:31)
*
0
P
(cid:0)
(cid:26)
$
(cid:6)
’
*
P
(cid:7)
(cid:8)
>
p
(cid:6)
(cid:31)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
[
(cid:129)
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:26)
$
%
(cid:6)
(cid:129)
)
*
9
Y
(cid:7)
(cid:8)
(cid:11)
.
8
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
[
&
(cid:6)
N
O
(
*
0
P
(cid:26)
@
3
(cid:13)

(cid:7)
(cid:8)
(cid:3)
%
@
(cid:31)
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:26)
$
&
H
(cid:129)
(
(cid:31)

*
0
P
(cid:7)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:31)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
[
&
N
O
(
(cid:15)
*
0
5
P
(cid:29)
(cid:19)
(cid:20)
@
3
x
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
$
%
N
(cid:15)
*
9
5
Y
(cid:0)
(cid:7)
(cid:19)
(cid:20)
3
x

(cid:16)
(cid:24)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
%
@
3
(cid:14)
(cid:31)
4
(cid:16)
9
X
:
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
r
$
&
(cid:6)
N
(
V
(cid:15)
*
0
5
P
(cid:11)
M
.
&
N
O
/
)
(cid:15)
*
0
5
P
(cid:29)
(cid:20)
.
3
O
8
)

(cid:2)
(cid:3)
U
T
3
8
)

9
:
(cid:2)
(cid:7)
#
(cid:29)
(cid:19)
T
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
>
(cid:29)
(cid:5)
7
&
(cid:30)
t
K

+
:
(cid:2)
(cid:7)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
l
N
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
‘
N
O
(
*
0
P
(cid:0)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:19)
.
3
(cid:14)
8
(cid:31)

(cid:16)
(cid:24)
(cid:2)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
l
(cid:6)
N
(
(cid:15)
*
0
5
P
(cid:20)
@
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
p
(cid:20)
(cid:6)
O
(cid:31)
(cid:15)
5
(cid:2)
(cid:8)
r
[
(cid:6)
N
O
(cid:31)
(cid:15)
*
5
P
(cid:11)
M
N
O
(cid:15)
*
5
P
(cid:0)
(cid:29)
(cid:19)
(cid:20)
3
(cid:21)
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
l
N
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
[
&
N
O
(
*
0
P
(cid:0)
(cid:5)
&
(cid:6)
(
(cid:31)
0
(cid:2)
(cid:7)
(cid:3)
(cid:11)
$
l
N
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
‘
N
O
(
*
0
P
(cid:0)
(cid:5)
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
l
(cid:129)
(
(cid:15)
*
0
5
P
(cid:0)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
$
l
(cid:129)
(
*
0
P
(cid:0)
(cid:7)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
p
(cid:12)
(cid:30)
(cid:13)
(cid:14)
(cid:31)
4
(cid:16)
(cid:17)
(cid:8)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
‘
N
(cid:14)
(
(cid:15)
e
+
(cid:17)
,
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
%
3
x

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
U
(cid:11)
(cid:19)
3
(cid:14)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:29)
(cid:19)
(cid:20)
%
&
3
x
(
V

(cid:16)
+
(cid:24)
:
7
@
N
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
&
’
(cid:14)
(
)
W
\
(cid:24)
Y
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
%
@
)
(cid:15)
9
5
:
(cid:0)
(cid:2)
(cid:7)
(cid:20)
.
(cid:21)
8
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:20)
(cid:13)
x
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:19)
(cid:20)
3
x
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:28)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
&
(cid:6)
(cid:129)
(
*
0
P
(cid:7)
#
(cid:29)
(cid:5)
(cid:30)
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
7
&
(cid:30)
t

+
:
(cid:2)
(cid:7)
#
(cid:29)
(cid:5)
%
(cid:30)
)

9
:
(cid:2)
(cid:7)
(cid:8)
7
&
t
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
2
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
%
@
(cid:13)
(cid:14)
(cid:31)
(cid:16)
9
(cid:24)
:
(cid:0)
>
(cid:4)
(cid:11)
$
N
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
>
(cid:19)
M
N
x
(cid:31)
e
(cid:24)
P
(cid:0)
>
(cid:4)
(cid:11)
$
N
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
(cid:19)
M
N
x
e
(cid:24)
P
(cid:0)
>
(cid:5)
(cid:19)
(cid:6)
(cid:14)
K
(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
(cid:129)
)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
l
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
@
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
.
(cid:30)
8
K

(cid:2)
(cid:7)
(cid:3)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:19)
(cid:20)
x
(cid:31)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:11)
(cid:19)
M
N
x
(cid:31)
(cid:15)
e
(cid:17)
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
l
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
(cid:19)
$
%
&
(cid:6)
N
(cid:14)
(
)
W
\
(cid:24)
(cid:26)
.
&
(cid:13)
t
)
0
(cid:0)
(cid:7)
(cid:3)
}
(cid:29)
.
3
8
K

(cid:2)
(cid:7)
(cid:3)
(cid:26)
$
7
&
(cid:129)
t
(cid:15)
*
+
5
Y
(cid:0)
#
(cid:29)
(cid:11)
(cid:20)
3
O
)
4
5
(cid:2)
(cid:8)
>
(cid:29)
(cid:20)
T
&
3
O
/
V

\
:
(cid:2)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:26)
@
3
(cid:13)
K
h
5
(cid:7)
(cid:8)
T
N
O
8
*
9
,
(cid:0)
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
‘
(
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:11)
(cid:26)
&
(cid:13)
(
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
$
%
&
’
(cid:14)
(
(cid:15)
W
\
(cid:17)
Y
(cid:20)
@
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
4
5
(cid:7)
(cid:8)
(cid:20)
%
&
O
(
+
:
(cid:0)
(cid:2)
(cid:29)
p
(cid:19)
(cid:30)
(cid:14)
4
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
%
l
(
)
\
:
(cid:0)
(cid:2)
(cid:7)
(cid:26)
.
&
(cid:13)
/
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:26)
%
&
(cid:13)
(
+
:
(cid:0)
(cid:7)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:26)
&
3
(cid:13)
(
V
4
0
5
(cid:7)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
h
5
(cid:7)
(cid:8)
(cid:20)
%
&
(cid:13)
O
(
\
:
(cid:0)
(cid:29)
r
H
h
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
$
%
&
(cid:6)
N
(cid:14)
(
e
+
(cid:24)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(cid:11)
(cid:19)
$
%
&
3
N
(cid:14)
(
4
W
\
X
(cid:19)
(cid:20)
%
(cid:21)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
U
(cid:11)
&
3
(
(cid:31)
h
0
5
(cid:2)
(cid:7)
(cid:19)
M
%
N
x
e
9
(cid:24)
Y
(cid:0)
(cid:4)
(cid:11)
(cid:19)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
@
3
x
V
4
(cid:16)
X
(cid:2)
(cid:8)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
U
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:5)
(cid:19)
$
%
(cid:30)
N
(cid:14)
)

W
9
(cid:24)
Y
(cid:5)
7
&
(cid:6)
t
)
+
:
(cid:2)
(cid:7)
(cid:29)
(cid:5)
.
H
8
)

(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
T
H
8
)

9
:
(cid:2)
(cid:7)
#
(cid:29)
T
3
8
)

9
:
(cid:2)
(cid:7)
>
(cid:29)
r
7
&
H
t
K
h
+
5
:
(cid:2)
T
N
O
8
*
9
,
(cid:0)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
$
@
N
V
(cid:15)
*
5
P
(cid:0)
(cid:7)
[
.
N
O
8
(cid:31)
*
P
(cid:0)
>
(cid:5)
$
(cid:6)
N
(cid:31)
*
P
(cid:7)
(cid:8)
>
(cid:4)
$
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
#
(cid:19)
$
N
(cid:14)
e
(cid:24)
P
(cid:0)
>
p
&
(cid:6)
(
(cid:31)
(cid:15)
0
5
(cid:2)
(cid:7)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
l
N
(
(cid:15)
*
0
5
P
(cid:0)
(cid:20)
@
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:5)
@
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
@
N
*
P
(cid:0)
(cid:7)
(cid:8)
#
(cid:19)
@
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
p
.
&
(cid:6)
t
(cid:31)
(cid:15)
0
5
(cid:2)
(cid:7)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
l
N
(
(cid:15)
*
0
5
P
(cid:0)
(cid:5)
(cid:19)
(cid:20)
(cid:6)
x
)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
.
(cid:6)
8
(cid:31)
(cid:2)
(cid:7)
(cid:3)
$
@
(cid:6)
N
*
P
(cid:7)
(cid:8)
#
(cid:5)
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
.
&
(cid:6)
t
(cid:31)
(cid:15)
0
5
(cid:2)
(cid:7)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
l
(cid:129)
(
(cid:15)
*
0
5
P
(cid:0)
>
(cid:26)
(cid:20)
(cid:13)
O
K
(cid:0)
(cid:8)
(cid:3)
(cid:26)
$
.
(cid:129)
8
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:26)
$
@
(cid:129)
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:4)
$
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:12)
$
&
(cid:6)
’
(cid:14)
(
(cid:31)
W
0
(cid:24)
$
@
’
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
‘
3
N
(cid:14)
(
h
e
+
(cid:17)
(cid:19)
(cid:20)
%
3
x

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:19)
%
@
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:11)
(cid:19)
@
3
(cid:14)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:29)
(cid:19)
(cid:20)
%
@
3
x
V

(cid:16)
9
(cid:24)
:
(cid:2)
7
@
N
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
&
’
(cid:14)
(
)
W
\
(cid:24)
Y
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:11)
.
&
t
)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:11)
(cid:20)
.
&
3
O
t
V
4
0
5
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
U
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
%
@
(cid:13)
(cid:14)
)
(cid:15)
(cid:16)
9
X
:
(cid:0)
(cid:20)
.
O
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:26)
%
&
(cid:13)
(
)
(cid:15)
\
5
:
(cid:0)
(cid:20)
.
&
O
t
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:4)
(cid:20)
O
(cid:31)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
$
N
(cid:14)
e
(cid:24)
P
(cid:0)
#
(cid:4)
(cid:19)
&
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
p
(cid:19)
.
&
(cid:6)
(cid:14)
t
)
(cid:15)
(cid:16)
0
(cid:17)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
%
&
(cid:13)
(
(cid:15)
\
5
:
(cid:0)
(cid:26)
(cid:20)
&
(cid:13)
O
(
(cid:15)
0
5
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
@
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
#
(cid:19)
.
(cid:14)
8
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
>
(cid:5)
.
&
(cid:6)
/
K
0
(cid:2)
(cid:7)
(cid:3)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:26)
%
&
3
(cid:13)
(
h
\
5
:
(cid:26)
(cid:20)
%
&
(cid:13)
O
(
(cid:15)
\
5
:
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
)
(cid:0)
(cid:8)
(cid:3)
(cid:26)
.
(cid:13)
8
)
(cid:0)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:11)
%
&
3
(
4
\
5
:
(cid:2)
(cid:29)
(cid:11)
(cid:20)
%
&
3
O
(
4
+
5
:
(cid:11)
(cid:20)
%
&
3
O
(
4
+
5
:
(cid:11)
(cid:19)
(cid:20)
%
3
(cid:21)
h
(cid:16)
9
(cid:17)
:
(cid:2)
(cid:11)
(cid:19)
(cid:20)
%
x
(cid:15)
(cid:16)
9
X
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:29)
(cid:12)
$
3
’
(cid:14)
V

W
(cid:24)
P
(cid:5)
$
T
&
(cid:6)
N
/
)
*
\
,
(cid:7)
}
(cid:29)
.
3
8
K

(cid:2)
(cid:7)
(cid:3)
$
7
&
N
t
*
+
Y
(cid:0)
(cid:7)
#
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
>
(cid:29)
p
T
&
(cid:30)
/
V
4
\
5
:
(cid:2)
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
$
%
@
N
(cid:14)
)
e
9
(cid:24)
,
(cid:0)
.
@
8
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
$
(cid:6)
N
*
P
(cid:7)
(cid:8)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
}
K
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
$
.
&
N
t
(cid:31)
*
0
P
(cid:0)
(cid:7)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
@
(cid:129)
(cid:14)
)
(cid:15)
e
X
P
(cid:0)
.
O
8
(cid:0)
(cid:2)
(cid:3)
U
(cid:11)
@
3
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
(cid:19)
M
%
N
x
e
9
(cid:24)
Y
(cid:0)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
r
(cid:19)
@
H
(cid:14)
h
(cid:16)
X
(cid:2)
(cid:8)
%
@
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:9)
(cid:7)
#
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
‘
(cid:13)
(
)
+
:
(cid:0)
(cid:7)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
&
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
(cid:5)
@
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
}
.
8
K
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
$
.
&
N
t
K
*
0
P
(cid:0)
(cid:7)
$
.
(cid:129)
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:5)
(cid:20)
(cid:6)
O
(cid:31)
(cid:2)
(cid:8)
(cid:3)
(cid:4)
(cid:26)
$
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:19)
$
(cid:6)
N
(cid:14)
W
(cid:24)
P
(cid:5)
(cid:19)
@
(cid:30)
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
4
W
9
X
Y
>
(cid:4)
(cid:20)
%
&
O
(
K
+
:
(cid:0)
(cid:2)
2
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
(cid:31)
4
W
X
[
%
@
N
(cid:21)
W
9
(cid:24)
,
(cid:0)
>
(cid:4)
@
K
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
V
4
W
X
7
N
O
8
*
9
Y
(cid:0)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
$
%
@
(cid:6)
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
U
(cid:11)
‘
3
(
V
h
0
5
(cid:2)
(cid:7)
(cid:19)
M
7
N
x
8
(cid:15)
e
9
(cid:17)
Y
(cid:29)
(cid:20)
3
O
(cid:31)

(cid:2)
(cid:8)
(cid:3)
#
(cid:4)
$
%
&
N
(
)
*
\
Y
(cid:0)
(cid:7)
#
(cid:19)
.
&
(cid:14)
t
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
#
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:19)
&
(cid:14)
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:20)
l
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:26)
(cid:13)
)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
.
(cid:6)
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:2)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:26)
&
(cid:13)
(
)
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:19)
(cid:20)
.
(cid:21)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
2
(cid:26)
3
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
$
%
(cid:6)
N
(cid:14)
e
9
(cid:24)
,
>
(cid:29)
(cid:5)
(cid:26)
&
H
(cid:13)
(
V

0
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
&
N
(cid:14)
(
(cid:15)
W
\
X
Y
(cid:4)
(cid:11)
(cid:19)
(cid:20)
&
x
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
.
3
x
8
(cid:31)
4
(cid:16)
X
(cid:2)
M
%
N
O
*
9
Y
(cid:0)
(cid:8)
>
U
@
3
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:11)
(cid:19)
$
7
3
N
(cid:14)
8
(cid:31)
4
W
9
X
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
(cid:29)
(cid:19)
.
3
(cid:14)
8
)

(cid:16)
(cid:24)
(cid:2)
(cid:28)
T
&
/
V
\
:
(cid:0)
(cid:2)
(cid:7)
$
.
&
(cid:129)
/
*
0
P
(cid:0)
(cid:7)
#
U
3
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:23)
T
&
3
(cid:13)
(cid:14)
/
V

(cid:16)
\
(cid:24)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
$
%
@
’
(cid:14)
(cid:15)
W
9
(cid:17)
Y
(cid:0)
(cid:20)
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
.
3
8

(cid:2)
(cid:7)
(cid:3)
%
@
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:29)
p
(cid:30)
4
5
(cid:2)
(cid:7)
(cid:8)
(cid:29)
(cid:20)
%
3
O
)

9
:
(cid:2)
(cid:8)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
%
l
(cid:6)
(
)
(cid:15)
\
5
:
(cid:2)
(cid:20)
.
O
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
#
(cid:26)
%
(cid:13)
)
9
:
(cid:0)
(cid:7)
(cid:8)
>
(cid:11)
.
&
t
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:11)
M
N
O
(cid:15)
*
5
P
(cid:0)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
&
(cid:13)
(
(cid:31)
0
(cid:0)
(cid:7)
(cid:3)
(cid:11)
(cid:26)
$
&
’
(
(cid:15)
*
0
5
P
(cid:0)
(cid:29)
(cid:19)
(cid:20)
3
x

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:26)
%
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:4)
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
p
(cid:19)
‘
(cid:30)
(cid:14)
(
4
(cid:16)
0
(cid:17)
(cid:2)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
2
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:12)
%
3
(cid:13)
(cid:14)

(cid:16)
9
(cid:24)
:
%
l
(cid:13)
(
\
:
(cid:0)
(cid:7)
(cid:29)
(cid:5)
H
)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
T
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:12)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
&
H
(
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(cid:11)
(cid:19)
$
%
3
N
(cid:14)
)
4
W
9
X
Y
(cid:20)
7
(cid:21)
8
(cid:16)
9
(cid:24)
:
(cid:0)
>
(cid:4)
(cid:11)
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
[
3
N
(cid:21)
4
W
X
P
(cid:4)
(cid:19)
(cid:20)
%
(cid:21)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
.
3
(cid:14)
8
(cid:31)
4
(cid:16)
X
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:12)
$
%
&
’
(cid:14)
(
)
W
\
(cid:24)
Y
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
U
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
%
@
(cid:13)
(cid:14)
)
(cid:16)
9
(cid:24)
:
(cid:0)
.
(cid:6)
8
(cid:15)
5
(cid:2)
(cid:7)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
p
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
p
%
(cid:6)
)
(cid:15)
9
5
:
(cid:2)
(cid:7)
(cid:20)
.
&
O
/
(cid:31)
0
(cid:0)
(cid:2)
(cid:3)
(cid:26)
$
(cid:129)
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:26)
$
&
(cid:129)
(
(cid:31)
*
0
P
(cid:0)
(cid:7)
#
(cid:26)
$
&
(cid:129)
(
)
*
0
P
(cid:0)
(cid:7)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
=
(cid:28)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:26)
$
&
(cid:129)
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
(cid:12)
[
3
’
(cid:21)

W
(cid:24)
P
%
@
3

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:19)
%
@
3
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:11)
(cid:19)
%
@
(cid:14)
(cid:15)
(cid:16)
9
X
:
(cid:0)
(cid:2)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
#
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
%
‘
3
(cid:13)
(

+
:
(cid:7)
%
@
)
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
7.2.2.4

ANSWERS TO EXERCISES

89

·

intersected moves. There are 8
5 cycles that have only 69(!) total intersections. And —
again uniquely(!) — it’s possible to have a total of 126. (See Fig. A–19(f, r, x). The tour
with 126 crossings had been known [FGbook page 495], but not its uniqueness.)
8 knight’s cycle has intersections of all four types, indeed at least 14

’s,
8
’s. Examples of those minima, which are attained in (376, 40,
896, 8384) ways, appear in Fig. A–21(a, b, c, g). On the other hand, Fig. A–21(d, e, f, j)
exhibits remarkable (and even more rare) tours where each ﬂavor of intersection is
maximized, namely (59, 44, 31, 30) intersections, in just (16, 120, 1160, 16) ways.

Every 8
’s, 4

×
’s, and 8

author
author
unique
Beluhov
Jelliss
mosaics
author

Figure A–21(j) is particularly striking, because all but four of its 64 moves are
! (The author had conjectured, in FGbook page 502, that such a tour
half of an
was essentially unique; this, however, is the other solution. Incidentally, N. I. Beluhov
[arXiv:1310.3450 [math.CO] (2013), 7 pages] had proved that no m
n knight’s tour
consists entirely of

moves.)

×

Figure A–21(l) is perhaps even more startling: All but four of its moves are part
! And all but ten of the moves in Fig. A–21(i) are part of at least
! Moreover, Fig. A–21(k) goes all the way: Every move in that cycle is part
intersection, indeed sometimes three or four! Altogether (688, 1864,

of at least one
one
of at least one
10408) tours achieve those remarkable feats of Fig. A–21(l), (i), and (k).

Finally, Fig. A–21(h) is one of 48 cycles for which only 23 moves are part of a
(Instances of the 40 and 896 cycles for which only 16 and 8 moves are part of an
and part of an

, respectively, are left to the reader’s imagination.)

.

163. Each cell of the board can be partitioned into 21 subregions, and we can compute
the winding number of each subregion by choosing an appropriate point in that subre-
gion and counting how often the tour crosses a straight line to the left of that point.
(Downward counts +1; upward counts
1.) The area of each subregion is a multiple
of

1
120 , so the calculation can work entirely with smallish integers.

−

[See the online program SSHAM-WINDING-PREP. This way to represent tours
by shaded regions was discovered by George Jelliss, who called them “knight’s tour
mosaics” and communicated his idea to the author on 26 December 1992. In that same
letter he asked if the minimum shaded area could be computed. Yes, now it can!]

1772
120 and

The fascinating extremal results are exhibited in Fig. A–22, where tours (a)
3942
and (b) attain the minimum and maximum shaded area (
120 ), while (c) at-
tains the maximum swept area (150). All three of those solutions are unique, except
for rotation and/or reﬂection. The 49 individual winding numbers at interior corners,
shown below each ﬁgure, yield the total swept area when we add them up, as proved in
exercise 164. Fig. A–22(d) shows one of the 254,652 tours for which those 49 numbers
take only two distinct values (possibly all 1 and 2). If we restrict consideration to the
1838
129,937,524,256 tours whose swept area is zero, the min and max shaded area (
120 and
3828
120 ) occur uniquely in tours (e) and (f). Tour (g) is one of 3,378,536 cases where the in-
terior winding numbers vary over a range of ten digits (in this case
5 through +4). And
the amazing and unique example (h) has only six nonzero interior winding numbers!

−

164. In fact this is true of any oriented polygonal cycle C whose vertices are a subset
of the midpoints of square cells, provided that none of the lines between consecutive
vertices goes exactly through a corner between cells. (See The American Mathematical
Monthly 101 (1994), 682–683; 104 (1997), 669; the proof consists of showing that such
cycles can nicely be “spliced together.”)

165. Yes; in fact, a census shows that there are 103,361,177,080 solutions(!). The
8 knight’s cycle, is 34; there
maximum number of moves with a given slope, in an 8

×

December 4, 2025

90

ANSWERS TO EXERCISES

7.2.2.4

(a)

(b)

(c)

(d)

historical note

1 2 0 2 1 ¯1 1
1 0 2 0 0 0 0
¯2 0 0 0 0 1 0
0 ¯1 0 0 0 ¯2 0
1 0 0 0 ¯2 ¯2 ¯1
0 1 0 ¯2 ¯2 ¯1 0
1 0 0 0 ¯2 0 1

1 0 ¯1 1 1 2 1
¯1 ¯1 ¯1 ¯1 3 2 1
¯1 ¯1 ¯1 1 1 1 1
¯1 ¯1 ¯1 ¯1 ¯1 ¯1 ¯1
¯2 ¯3 ¯1 ¯3 ¯3 ¯3 ¯2
¯1 ¯1 ¯1 ¯1 ¯3 ¯4 ¯1
¯1 0 1 ¯1 ¯2 ¯1 ¯1

1 2 1 2 2 2 1
2 4 4 4 4 4 2
2 4 5 6 5 3 2
1 4 5 7 5 4 1
2 4 5 6 5 4 2
2 4 4 3 4 4 2
1 2 1 2 1 2 1

1 1 0 0 0 0 1
0 1 0 0 1 1 0
0 0 1 1 1 0 1
1 1 0 1 0 1 1
1 0 1 1 1 0 0
0 1 1 0 0 1 0
1 0 0 0 0 1 1

(e)

(f)

(g)

(h)

1 0 1 0 ¯2 1 1
0 2 0 ¯1 0 0 2
2 0 0 0 0 2 0
0 1 0 0 0 0 0
¯1 0 0 0 0 ¯2 0
0 ¯1 0 0 0 ¯1 ¯2
¯1 0 0 0 0 ¯1 ¯1

1 ¯1 0 1 1 1 ¯1
0 1 1 1 1 1 0
1 1 1 1 1 1 1
0 0 0 1 1 0 ¯1
¯1 ¯1 ¯1 ¯1 ¯1 ¯1 ¯1
0 ¯1 ¯1 ¯1 ¯1 ¯1 0
¯1 0 1 ¯1 ¯1 0 ¯1

1 2 2 0 ¯1 2 1
1 4 2 0 0 0 2
2 2 1 0 ¯1 0 ¯1
1 0 ¯1 ¯2 ¯2 ¯3 ¯1
¯2 ¯1 ¯1 ¯3 ¯5 ¯4 ¯1
¯1 ¯2 ¯2 ¯3 ¯3 ¯4 ¯2
1 ¯2 ¯2 0 ¯1 ¯2 ¯1

Fig. A–22. Record-breaking winding number patterns of closed 8

1 0 ¯1 0 0 0 ¯1
0 0 0 0 0 0 0
0 0 0 0 0 0 0
0 0 0 0 0 0 0
0 0 0 0 0 0 0
0 0 0 0 0 0 0
¯1 0 0 0 0 ¯1 1
8 tours.

×

are 4116 such tours, one of which is Fig. A–19(f). The minimum number is 2, achievable
in 59124 ways (and easily ﬁndable by removing 40 edges from the knight graph).

[Parmentier’s early survey of knight’s tours was published by Association fran¸caise
pour l’avancement des sciences as a supplement to the proceedings of their Congr`es de
Marseille (1891), 24 pages and xi plates; Fig. 23 on plate iii exhibited an open tour
with 36 moves of slope
170. Vertices 15 and 16 are endpoints; 17 is inner; 18, 19, 20 are bare. That forces a lot:

1/2.]

−

17

19

18

1

2

20
16

4
8

12

14

10

11

5

;

3

6

7

9

15

13

December 4, 2025

17

19

18

1

2

20
16

4
8

12

15

13

14

10

11

5

.

3

6

7

9

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
wedges
Pettersson
border structure, see marked involution
ranking
unranking
OEIS
saddle point method
notation

m

(cid:4)→

7.2.2.4

ANSWERS TO EXERCISES

91

(When Algorithm E proceeds to 15-conﬁgs, these two answers yield 17-cycles of G17.)

171.

d
2

, when vertex 1 has degree d. (They’re the possible wedges of vertex 1.)

(cid:15)

(cid:16)

172. There aren’t any, unless n = 1. (The only possible endpoint is ‘n’.)
173. From ¯1101 and ¯111¯1 we get 101 and 11¯1. (The classes of 17-conﬁgs have three-
F17 = (18, 19, 20).) From 0110 we get nothing. Class 1001 yields
digit names, because
additional members of 101; class 101¯1 yields additional members of 11¯1; class 1212
yields an additional class, ¯111. Each of the three 17-classes therefore has size 10. (And
ultimately they’ll account for the thirty 20-cycles, as in the next exercise.)
174. In the 17-class 11¯1, vertices 18 and 19 are endpoints of a subpath, while vertex 20
is inner. Joining 18
19 C20.)

19 completes a cycle of G20. (Similarly, 101

18 11

(cid:7)

−−−

(cid:4)→

(cid:4)→

176. (a) Let k in the sum be the number of unmarked elements.

−

1 ways for n to be in a 1-cycle; (n

2 ways for it to be in a 2-cycle.
(b) 2Tn
(c) There are exactly Tq possible names. When q = 2, for example, the ﬁve possi-
ble names ¯1¯1, ¯10, 0¯1, 00, 11 correspond naturally to the ﬁve possible marked involutions.
[See V. H. Pettersson, Electronic J. Combinatorics 21 (2014), #P4.7, Theorem 13.
2.4.1 gave methods for ranking and unranking the nth order marked involutions.

His
Marked involutions occur also in many other contexts; see OEIS A005425.]

1)Tn

−

§

−

177. The methods of Section 5.1.4 apply, with Tn(k) = 2
1
‘2(k + 1)’ becomes ‘8(k + 1)’ and ‘
2 n
and (44). Appropriate changes to the subsequent formulas lead to

√n )’ becomes ‘

1
2 (n

−

−

−

n

2k

tn(k). For example,
√n ’ in Eqs. 5.1.4–(43)

Tn =

1
√2

n

n/2

e−

n/2+2√n

1

−

(1 +

1/2

5
6 n−

+ O(n−

3/4

)),

a bit more than

n!. One can also use the saddle point method as in exercise 7.2.1.5–51.

178. The largest possible digit aj of a marked involution is
possible digit of a MATE table is q.

(cid:18)

q/2

(cid:16)

(cid:17)

, while the largest

179. (a) (Assume that error checking is unnecessary.) Set HIT[k]
Then do this for k = 1, . . . , q: Set j
HIT[j] = 0, set HIT[j]

k; otherwise set MATE[HIT[j]]

←
0, set MATE[k]

ak; if j

←
k, MATE[k]

←

≤

≤

k
q/2.
j; otherwise if
HIT[j].

≤

0 for 1

(b) Set t

0 and do this for k = 1, . . . , q: Set j

←

←

←
MATE[k]; if j

←
0, set ak

←

≤

j;

←

otherwise if j > k, set t

t + 1, aj

ak

t.

←
181. (i) Suppose m + 1 = u(cid:2)j, where j > 0. Then (u1, . . . , uq0 ) is a permutation of
. (ii) In this case m + 1 = u(cid:2)0,

, 1τ = j, and q0 = q(cid:2)

Fm

←

←

1

(cid:0)

u(cid:2)2, . . . , u(cid:2)q
{
(u2, . . . , uq0 ) is a permutation of

}

Fm
1 =
−
|
(cid:0)
u(cid:2)2, . . . , u(cid:2)q
(cid:7)

}

{

−
, 1τ = 0, and q(cid:2) = q0.

∩

|

(cid:7)

183. The only 0-class is ‘0’. Figure A–23, too big to ﬁnd by hand in a reasonable time,
m β that hold in K6; we get the relations for K5 by ignoring all
shows all relations α
class names that don’t end with 0 (and by erasing the ﬁnal zero when they do).

(cid:4)→

3 C6; 01¯11
(cid:4)→
4 C6; 1¯11

There also are cases where α
3 C6; 011¯1

3 C4;
2 C4; 1100
(cid:4)→
0¯111
3 C5; 11¯10
3 C5;
011
5 C6. (They account for the
(cid:4)→
facts that the number of Hamiltonian (3, 4, 5, 6)-cycles is (1; 1+2; 2+2+2+6; 2+2+2+
6+12+12+24) = (1, 3, 12, 60), in agreement with exercise 105(a).)
c

m Cp: 11000
3 C6; 0110

(cid:4)→
3 C5; 1¯110

(cid:4)→
4 C6; 11¯1

(cid:4)→
4 C5; 11

2 C3; 01100

4 C6; 110

(cid:4)→
(cid:4)→

(cid:4)→
(cid:4)→

(cid:4)→

(cid:4)→

(cid:4)→

(cid:4)→

(cid:4)→

m

n

a

2

b

b

184. The (m
a
and p = m + a + b + c + 2. (ii) 1¯1

a
1¯1
1) class α has two forms: (i) 0¯1
0
1
b
−
−
, where a, b

1¯1

1¯1

−

0

m

−

−

−

n

a

c

b

−

−

−

−

, where a, b, c
0
0 and p = m + a + b + 1.

≥

≥

December 4, 2025

92

ANSWERS TO EXERCISES

7.2.2.4

0

consecutive 1s
Gessel
sparse-set manipulations
insertion sort

00011

00101

00110

01001

01010

01100

10001

10010

10100

11000

¯1011 ¯1101 ¯1110 0¯111 0011 01¯11 0101 011¯1 0110 1¯101 1¯110 10¯11 1001 101¯1 1010 11¯10 110¯1 1100 1122 1212 1221

¯111

011

1¯11

101

11¯1

110

Fig. A–23. Transitions between 0-classes, . . . , 4-classes when Algorithm E does K6.

11

r

−

185. Encoding vertex v by ‘[v > m]’, we see that F (m, r, s, t) = m! r! G(m, r, t), where
G(m, r, t) is the number of solutions to the following problem: “Construct t binary
strings from m 0s and r 1s, where each string begins and ends with 0 and has no two
consecutive 1s.” Equivalently (after replacing ‘10’ by ‘1’), “Construct t binary strings
r 0s and r 1s, where each string begins with 0.” Equivalently, “Construct
from m
t 0s and r 1s, where each string might be empty.”
t binary strings from m
−
t, containing exactly r 1s, and
Equivalently, “Construct a binary string of length m
1
m
−
factor it into t possibly empty substrings.” Hence G(m, r, t) =
t
1
−
m

(cid:16)(cid:15)
[The classes in exercise 184 have r = a+b+c and t = 1, hence size
(cid:15)
(cid:14)

If we ﬁx p, the contributions to Cp from (i) are therefore f (p) =
(p
f nor g seems to have a simple closed form. But the fact that f (p) + g(p) = (p
n
leads to the identity
k
n
the summand is (n
k

2
(cid:16)
−
r
4
p
−
(cid:16)
r=0(
×
(cid:16)
(cid:15)
2)! (r+1)). Neither
1)!/2
) = n!. Ira Gessel observes that

3)! (r+2)!)/2; from (ii) they are g(p) =

1)! r!.
(m
−
4
r
p
−
−
r

, which telescopes.]

−
1))! (k

(cid:14)
n
+

n
1
−
k=1 (n

p
3
−
r=0(

(cid:16)
k)! k!

(cid:15)
1
−
1

r
−

m
−
r

(cid:14)
(k

(cid:15)
(n

(p

−

−

−

−

−

−

k
k

−
k

r
r

(cid:15)

(cid:16)

r

−

−

−

−

−

n

k

p

.

3

1

t

−

−

−
−
FR[k] for 1
IFR[m+1] and q
FR[q], FR[0]

←

≤
←
←
t. Otherwise set FR[0]

(cid:15)
k < q. (At this point we always have q = q(cid:2).)
q
−
m + 1, IFR[m+1]

1. If t < q (that is, if m + 1 is in

0, FR[q]

(cid:16)

←
m + 1, IFR[m+1]

←

187. Set OFR[k]
Set t
the last), set x
FR[t]
←
IFR[m]

←

←

x, IFR[x]

←

t; and if t

= q, set q

q + 1 (thereby retaining the last element of

←
Set q0
q, set x

←
q. For all vertices v > m such that m
q, FR[t]
FR[q], FR[q]

v, IFR[v]

←

←

←
←

t

≥

v, do this: Set t
x, IFR[x]
t, q

←

−−−
←

Now do a simple insertion sort to establish (30): For k = 2, . . . , q0

←

←

Fm

−
m, IFR[m]
(cid:7)
0, FR[t]

1 but isn’t
q,
←
m,
←
Fm
1).
−
IFR[v]; if
(cid:7)
q + 1.
1, sortin(k, 0);
1],

←
←

−

for k = q0 + 1, . . . , q
do this: Set t
j + 1, and j

−
FR[k], j

1, sortin(k, q0). Here ‘sortin(k, l)’ means “If FR[k] < FR[k

k

1; repeatedly set FR[j + 1]

−
FR[j], IFR[FR[j]]

←
j

←
j + 1.”
To compute σ and τ we use arrays SIG and TAU, where jσ = SIG[j + 1] for
SIG[2]

1 until j < l or FR[j] < t; set FR[j + 1]

1: Set SIG[0]

0; SIG[j + 1]

t and IFR[t]

0, TAU[1]

1, SIG[1]

←

←

←

←

←

−

−

← −

←

←

←

←

j

≥ −

k)! k! (
(cid:15)
1)!
(cid:15)

−

−
−
−
−

k
1
k
(cid:16)
1
(cid:16)

December 4, 2025

(cid:12)
7.2.2.4

ANSWERS TO EXERCISES

93

1 + IFR[OFR[j
arrays by setting BMATE[k]

−

←

1]] and TAU[SIG[j + 1]]

j, for 1 < j

q(cid:2). (Step E4 uses those

≤
SIG[1 + OMATE[TAU[k]]] for 1

←

Set r

0. Then, for all vertices v > m such that m

←

←
r + 1. (At this point we should also set up FMAP; see answer 193.)

−−−

1+IFR[v]

k

q0.)
≤
v, set NBR[r]

≤

BMATE
overﬂow
basic mate table
OEIS

←
←
p(cid:2)l

−

0; exit the loop if l = q(cid:2);
l + 1, a(cid:2)l
j
1; repeat.
−
a(cid:2)l + 2; while
1 and j
OMEM[t][j],
1, t
j

←
←
←

and r
←
189. In E3, set t
while OMEM[t][j] = 0, set j

←

←

l

←
In E8, begin the following loop with l

←

0 and do this loop: Set p(cid:2)l
j + 1; set t

t and j
←
OMEM[t][j], l
q(cid:2): Set t

←
j + 1; if j < Δ, set a(cid:2)l

←

l

−

≤

−

←

←

←

0 and p

MEM[0][2]

j < Δ, MEM[t][al + 1]

←
1, and repeat this loop if l > 0.

←
←
←
←
(cid:0) ] to WT[t(cid:2)]; otherwise set w

1. Set t
←
MEM[t][al + 1]; exit if l = q; if t(cid:2) > 0, set t
p, and p

j < Δ and OMEM[t][j] = 0 set j
and exit to the E3 loop; otherwise set l
←
191. Use exercise 179(b) to compute the class name a1 . . . aq. If p = 0, set MEM[0][0]
MEM[0][1]
t(cid:2)
←
for 0
Then if t(cid:2) > 0, add OWT[p(cid:2)q
OWT[p(cid:2)q
WT[w]
and that p and w don’t overﬂow memory bounds.)
192. True. Suppose OMATE[1] = k > 0. Then 1 < k
(36) and (37), because 1
by (38). And OMATE[k] = 1. [“The mate of m in an (m
basic mate table of the associated m-conﬁg.”]
193. (This is the “heart” of Algorithm E.) Set MATE[k]
≤
Do nothing if MATE[i] < 0 or MATE[j] < 0. (Vertices ui and uj must not be inner.)

q(cid:2); and u(cid:2)k = ukσ = u(cid:2)kστ by
q0. Hence BMATE[kσ] = OMATE[kστ ]σ = OMATE[k]σ
1)-conﬁg becomes bare in the

←
1, and do this loop: Set
0
l + 1 and repeat.
w,
q,

0, l
t(cid:2), otherwise set MEM[p][j]
p + 1; set l

(cid:0) ]. (In practice we should also ensure that al + 1 < Δ for 1

w + 1, MEM[t][aq + 1]

BMATE[k] for 1

←
l
≤

p, t

kσ

←

←

←

←

←

←

←

≤

≤

≤

−

≤

≤

q.

k

in step E7! See exercise 192.) Otherwise set MATE[i]

Case 1: MATE[i] = MATE[j] = 0. If i = j, do the cycle test below. (That can happen
i, and contribute().
1,

←
Case 2: MATE[i] = 0 < MATE[j] = k. Set MATE[i]

←
k, MATE[k]

j, MATE[j]

i, MATE[j]

and contribute(). (Vertex uj becomes inner.)

Case 3: MATE[j] = 0 < MATE[i] = k. Set MATE[j]

and contribute(). (Vertex ui becomes inner.)

←

←

← −

k, MATE[k]

j, MATE[i]

1,

← −

←

←

←

l, MATE[l]

k, MATE[i]

Otherwise set MATE[k]

Case 4: MATE[i] = k > 0 and MATE[j] = l > 0. If j = k, do the cycle test below.
1, and contribute().
Cycle test: A cycle cannot be in an m-conﬁg; but the new connection between
(cid:0)
. The latter occurs if and only if (i) all
m(cid:2) are inner; and (ii) all vertices > m(cid:2) are bare. To implement this test,
1 such that either k > q0
1] = m + k, and if MATE[k(cid:2)] = 0 for

ui and uj might complete an m(cid:2)-cycle in Gm
vertices
ﬁrst set MATE[i]
or MATE[k]
k(cid:2)
k

← −
−
(cid:0) ] to CYC[m + k

0 or FR[k
q, add OWT[p(cid:2)q

1. Then ﬁnd the smallest k

= m + k. If FR[k

MATE[j]

MATE[j]

← −

1].

1]

←

←

←

≥

≤

≥

−

≤

≤

(Proof sketch: Frontier vertices uk for q0 < k

−

≤

q cannot be in the cycle, because
1] = m + k

k

−

≤

≤

−

m(cid:2)

≤
1 for 1

m is m itself. Consequently we must have FR[k

their only neighbor
m; also MATE[k] = 0 for m(cid:2)
and MATE[k] =
195. In general, the digits aj in a class name belong to the set
the frontier has size q. So we need Δ
graph for which the digit
hence Δ
196. There are four solutions, one of which is shown.
rithm E sets CYC[26]
CYC[28]
CYC[38]
CYC[46]

←
12, CYC[30]
101730, CYC[40]
←
69362264, CYC[48]

(Consequently Algo-
4. These are the smallest cycles that it ﬁnds. It also sets
4525,
←
2408624,

10 is suﬃcient. (And necessary, as seen in exercise 198.)

←
55488142, etc.; see OEIS A383664.)

when
+ 2, unless we’re lucky enough to have a
17;

−
m < k
−
¯1, 0, . . . ,
{

(cid:17)
is never needed. The 8

32 knight graph has q

44202, CYC[42]

66034, CYC[44]

212, CYC[32]

50, CYC[36]

≤
q/2
(cid:16)

0, CYC[34]

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:24)1

(cid:9)](cid:23)

(cid:9)](cid:8)

(cid:9)#$

(cid:7)/$

(cid:3){(cid:23)

(cid:3)6(cid:8)

(cid:9)UC

(cid:3)XC

(cid:9)S’

(cid:9)E(cid:31)

(cid:9)TC

(cid:3)d(cid:0)

(cid:9)(cid:128)V

(cid:3)c(cid:23)

(cid:9)B(cid:0)

(cid:9)_0

(cid:8)(cid:18)(cid:23)

(cid:3)](cid:0)

(cid:9)zC

>Ow

(cid:3)N(cid:0)

(cid:9)Ub

(cid:9)X2

(cid:9)l(cid:0)

≥ (cid:16)

q/2

q/2

q.)

←

←

←

←

(cid:17)}

≥

×

≤

(cid:16)

(cid:17)

←

←
←
←

December 4, 2025

(cid:12)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
1
m
(cid:13)
(cid:14)
(cid:15)
(cid:16)
n
(cid:0)
(cid:8)
(cid:12)
(cid:19)
(cid:13)
p
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:13)
(cid:20)
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
%
(cid:31)
(cid:5)
^
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
F
(cid:31)
1
(cid:23)
&
’
(
;
a
*
W
H
,
L
(cid:21)
>
(cid:31)
(cid:19)
=
(
;
(cid:20)
3
W
"
-
M
(cid:2)
=
(cid:13)
A
:
M
(cid:0)
(cid:7)
(cid:9)
(cid:7)
C
(cid:30)
(cid:31)
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
&
’
|
8
*
,
-
.
(cid:0)
(cid:7)
(cid:31)
(cid:23)
;
(cid:13)
"
(cid:7)
(cid:8)
(cid:3)
:
M
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:8)
(cid:9)
(cid:7)
C
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
1
(cid:12)
G
;
(cid:13)
(cid:14)
H
(cid:16)
(cid:17)
(cid:8)
(cid:19)
’
(cid:20)
:
M
(cid:0)
(cid:2)
(cid:8)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
F
(cid:31)
(cid:5)
^
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
’
(
(cid:6)
*
W
-
M
(cid:2)
(cid:7)
2
(cid:13)
A
(cid:0)
(cid:7)
(cid:3)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
C
0
(cid:5)
(cid:6)
!
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:31)
y
(cid:23)
&
^
)
!
H
,
(cid:21)
5
(cid:7)
7
’
a
(cid:20)
,
:
.
(cid:0)
(cid:8)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
%
P
;
!
"
(cid:2)
(cid:7)
(cid:8)
(cid:3)
0
(cid:31)
1
(cid:25)
&
’
K
;
8
(cid:14)
*
!
\
R
L
n
’
G
8
(cid:20)
,
:
>
(cid:0)
(cid:8)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
C
F
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
|
*
W
4
(cid:0)
(cid:2)
(cid:7)
(cid:3)
G
A
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
canonical notation
class names
X cuts

94

ANSWERS TO EXERCISES

7.2.2.4

197. board (p, q, 0, 0, 5, 0, 0) is a graph of knight moves with pq vertices named ‘i.j’,
and they appear in lexicographic order: 0.0, 0.1, . . . , 0.(q
1).
1) together with 1.j and 2.j for
So the frontier
all j. Furthermore, all frontiers have at most 2q + 1 vertices, regardless of p.

1 has 2q + 1 vertices, namely 0.(q

1), 1.0, . . . , (p

1).(q

Fq

−

−

−

−

−

Therefore Algorithm E fares poorly when q > p. Conversely, with the graph
board (32, 8, 0, 0, 5, 0, 0), we do get the desired frontiers (41) — but we must realize that
the vertex for row i and column j has the SGB name ‘j.i’, not ‘i.j’.

(cid:7)

198. (a) For m mod 8 = (0, 1, . . . , 7), respectively (1187898716, 411619845, 565860079,
1335885051, 1525183477, 1964090779, 2084942265, 1977893280); that’s about (4.20,
1.76, 1.48, 2.90, 2.56, 3.27, 2.51, 2.37) contributions per class.

(b) Only rarely:

(2, 0, 0, 4, 5, 2, 4, 2), respectively(!). For example, the
(8m + 2)-class 0¯1¯1¯1¯1¯11¯1¯1¯11¯100000 updates CYC[8m + 14]; so does the (8m + 7)-class
1¯1¯1¯1¯1¯110000000000, while 1¯1¯1¯1¯1¯11¯1¯100000000 updates CYC[8m + 16].

(c) (i) 1, occurring ﬁrst in class ¯1¯1¯1¯1¯1¯1¯1¯10011¯1¯122; (ii) 1, occurring ﬁrst in
class 1233245165788764; (iii) 655752828068, occurring ﬁrst in class 1233456146788725;
(iv) 51496469055038078292944, occurring ﬁrst in class 1233456146788725.

(d) (i) 2320688; (ii) 225507902921136492; (iii) 17497529967689449592414967040;

(iv) 1340796579503792035593107143277586339820; all in class 0¯1¯1¯1¯1¯1¯1001000010.

(e) m = 71, occurring ﬁrst in class 12345316507684287.
(f) m = 40, class 0¯1¯1¯1¯1¯1¯1001000010 has weight 1643851174.
(g) ¯1¯1¯1¯1¯1¯1¯1¯10¯1¯10¯1¯111; ¯1¯1¯1¯1¯1¯1¯10¯1¯1¯1¯1¯1101; ¯1¯1¯1¯1¯1¯10¯1¯1¯1¯1¯110100; ¯1¯1¯1¯1¯1¯1¯1¯1¯1¯1¯1¯110-
010; ¯1¯1¯1¯1¯1¯1¯1¯1¯1¯1¯1000101; ¯1¯1¯1¯1¯1¯1¯1¯1¯1¯1000¯1011; ¯1¯1¯1¯1¯1¯1¯1¯1¯1¯10¯1¯10011; ¯1¯1¯1¯1¯1¯1¯1¯1¯10¯1¯10¯1101.
200. (a) 1231432004000000; 12342100430000000; 12314403200000000; 12344321000-
000000; 12332140040000000; 12213400430000000; 11234204300000000. (The canonical
notation for class names is not intuitive! For exercises such as this, it would be better
to keep track of the endpoints of the four subpaths: If α0 is abcdbadc000000, then α1
is bcdbadc00a000000, and α2 is cdbadc00ab0000000, etc.)

(b) 1¯123145056040236; ¯11234505634012600; 12345056340120600; 12340452306-

105006; 12303¯112045050040; 1202¯1310450500403; 101¯12304505004023.
201. 1234156473762858, 1234156743267858, 1234567483812765, 1234567843218765.

202. If α0 = a1 . . . a16 and t = max
, a periodic tour based on α0 will
{
change direction 2t times, because it crosses column m/8 in both directions, for each
of t subpaths. Thus we want t = 8, as in exercise 201.

a1, . . . , a16

}

But none of the 8-classes in answer 201 is suitable for α0; they have no interme-
diate α1, . . . , α7. The only way to sustain a class with t = 8 is to make eight horizontal
X cuts (see exercise 160), and this requirement severely restricts α0.

There is a suitable 16-class, namely α0 = 1212343456567878; and we can use it

to obtain the solution shown.

Many other suitable classes exist. We might, for
example, have α0 = 1234562178654387. But that one is
diﬃcult to reach — it arises ﬁrst as a 40-class! In any case
all solutions will look the same: They’re mostly X cuts,
except for the patterns at the very left and the very right.

(cid:9)(cid:10)(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:11)

(cid:9)(cid:25)(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)(cid:25)(cid:8)

(cid:9)~"

(cid:0)Z"

(cid:9)1"

(cid:9)n"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:3)n#

(cid:9)1"

(cid:9)|(cid:26)

(cid:3)L(cid:8)

(cid:9)G"

(cid:9)A"

(cid:9)6(cid:4)

(cid:9)(cid:133)(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)=

(cid:9)i#

(cid:9)(cid:137)(cid:4)

(cid:9)(cid:22)=

(cid:9)GM

(cid:3)(cid:130)(cid:8)

(cid:9)(cid:10)(cid:4)

(cid:8)(cid:18)#

(cid:9)(cid:137)"

(cid:9)(cid:138)"

(cid:9)1"

(cid:9)n"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)n"

(cid:9)1p

(cid:9)w#

(cid:9)(cid:138)R

(cid:9)(cid:131)$

(cid:3)b(cid:8)

(cid:9)k"

(cid:3)Ǳ"

(cid:9)6(cid:4)

(cid:9)6(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:28)

(cid:9)(cid:138)(cid:4)

(cid:0)g(cid:5)

(cid:9)q(cid:26)

(cid:9)^(cid:8)

(cid:9)?(cid:11)

(cid:9)A#

(cid:9)(cid:138)"

(cid:9)(cid:137)"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)n"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)n#

(cid:9)1p

(cid:9)(cid:134)"

(cid:9)|(cid:26)

(cid:3)L(cid:8)

(cid:9)Z#

(cid:0)~(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)g(cid:4)

(cid:9)g#

(cid:9)(cid:137)>

(cid:9)(cid:22)=

(cid:8)iM

(cid:3)j(cid:8)

(cid:9)k"

(cid:9)m"

(cid:9)n"

(cid:9)1"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)1"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)1"

(cid:9)n#

(cid:9)nF

(cid:9)a.

(cid:9)b(cid:8)

204. Let OMEM now be simply an array of octabytes. We shall use a completely diﬀerent
way to set OMEM and OWT in step E2, after setting q(cid:2)
←
w(cid:2)
0; here PACK is an octabyte, and s is the number of bits that
have been packed into PACK. Call compress(0, 0), where compress(l, p) is the following

0: Set p(cid:2)

PACK

q, p

←

←

←

←

←

←

w

s

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:19)
$
%
&
N
(cid:14)
(
)
W
\
(cid:24)
Y
#
(cid:19)
.
&
(cid:14)
t
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
.
&
3
t
)

0
(cid:2)
(cid:7)
(cid:3)
#
7
&
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:11)
.
&
/
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
(cid:20)
&
H
O
(
V

0
(cid:2)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
@
(cid:13)
)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:20)
&
O
(
0
(cid:0)
(cid:2)
(cid:3)
>
(cid:29)
p
(cid:19)
(cid:30)
(cid:14)
(cid:31)
4
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
%
(cid:129)
(cid:14)
(cid:15)
e
9
X
,
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
#
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
(cid:6)
t
(cid:15)
0
5
(cid:2)
(cid:7)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
>
(cid:20)
&
O
(
V
0
(cid:0)
(cid:2)
(cid:3)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
$
%
‘
N
(
)
*
+
,
(cid:0)
(cid:7)
(cid:4)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
M
&
N
O
(
(cid:15)
*
0
5
P
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
=
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
@
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
#
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(cid:6)
(
(cid:15)
0
5
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
(cid:20)
H
O
V

(cid:2)
(cid:8)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
&
N
(cid:14)
(
(cid:15)
W
\
X
Y
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
(cid:20)
&
O
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
[
3
N
(cid:21)
(cid:31)
4
W
X
P
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
recursive procedure
hypohamiltonian graph
Holton
Sheehan
compression
hash function

∞bignum

7.2.2.4

ANSWERS TO EXERCISES

95

k

←

(cid:30)

←

←

←

←

b, s

Δ
1
−
k=0 2

PACK + (b

WT[p] and w(cid:2)

= 0]; if s + Δ > 64, set OMEM[p(cid:2)]

[MEM[p][k]
p(cid:2) + 1; else set PACK

←
PACK, PACK
←
←
s + Δ; then for 0

recursive procedure: If l = q, set OWT[w(cid:2)]
b
←
and p(cid:2)
(cid:14)
if MEM[p][k]
OMEM[p(cid:2)]

w(cid:2) + 1. Otherwise set
Δ,
←
k < Δ,
s) and s
= 0, call compress(l + 1, MEM[p][k]). When compress(0, 0) ﬁnishes, set
PACK. Conclude step E2 by changing FR, IFR, q0, and q as before.
Steps E3–E8 are eﬀectively replaced by an inverse process, which is invoked by
OMEM[0], and calling uncompress(0). Procedure
setting s
←
(cid:0) and controls the activities as follows:
uncompress(l) sets up the address digits a(cid:2)1 . . . a(cid:2)q
p(cid:2) + 1,
s + Δ; if s + Δ > 64, set p(cid:2)
If l < q(cid:2), set b
PACK
1 and
≤
call uncompress(l + 1). On the other hand if l = q(cid:2), uncompress(l) goes to step E4
(which transfers to either E5, E6, or E7). Our new algorithm no longer needs p(cid:2)0, . . . ,
(cid:0) ]. When control
p(cid:2)q
w(cid:2) + 1, and exit from uncompress(q(cid:2)).
reaches the former step E8, we simply set w(cid:2)

(cid:0) ; instead, we use OWT[w(cid:2)] where the former algorithm used OWT[p(cid:2)q

(PACK
←
OMEM[p(cid:2)], and s

s) & (2
0; then for 0

←
k < Δ, if b & 2

= 0, set al

←
k
−

0, PACK

(cid:31)
←

←
Δ

1), s

w(cid:2)

←

←

←

←

p(cid:2)

≤

−

k

←

2(cid:2)

−−−

205. (a) One 5-cycle (0
−−−
0(cid:2)
0).
4
2
−−−
[The Petersen graph is known to be the smallest “hypohamiltonian graph,” namely the
smallest non-Hamiltonian graph that becomes Hamiltonian when any vertex is deleted.
See D. A. Holton and J. Sheehan, The Petersen Graph (1993), Chapter 7.]

0); two 9-cycles (0
1

1
2
−−−
0 and 0

−−−
−−−

−−−
−−−

−−−
0(cid:2)

−−−
2(cid:2)

−−−
3(cid:2)

−−−
3

−−−
4

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

−−−

1(cid:2)

3(cid:2)

1(cid:2)

3

4

3

1

2

(b) (1, 1, 1, 5, 2, 1, 4, 30, 120) for m = (2, 3, 4, 5, 6, 7, 8, 9, 10). [The 7-path is
0

1(cid:2).]

3

2

1

4

−−−

−−−

−−−

−−−

−−−

0(cid:2)

−−−

206. Since each frontier gains an element, we need Δ = 11 to handle the frontiers of
size 18 (see exercise 195). And the number P of nonlief trie nodes will now be roughly
an order of magnitude larger than before; hence P will exceed 2
, and each address
of a trie or lief node must now be a 64-bit integer. (We were lucky in (40) to have P
1798400809, comfortably less than 2

≤
.) So trie nodes will now occupy 88 bytes, not 40.
The maximum Pm during the computation of (44) turned out to be approximately
15.5 billion, and the maximum class size Cm was about 7.9 billion. Hence RAM usage
per trie was about 1.7 terabytes. However, the compression scheme of exercise 204
reduced the total to 1.9 terabytes for both tries.

32

31

≥

207. Let h be a hash function that takes partial keys a1 . . . al for 0
l < q and
¯1 into [0 . . 8], say, and use nine trielike structures stored in MEM[0], MEM[1], . . . ,
aj
MEM[8], WT[0], WT[1], . . . , WT[8]. To ﬁnd the weight for a given key a1 . . . aq, start
MEM[h(a1 . . . al)][t][al+1 + 1],
with t
l

l + 1. The desired weight is then WT[h(a1 . . . aq)][t].

0 and do this loop while l < q: Set t

←

←

←

≤

l

With high probability the set of needed preﬁxes a1 . . . al with h(a1 . . . al) = k will
35

32

35

be approximately 2

/9, for 0

k

8. And 2

/9 is comfortably less than 2

.

←

≤

≤

∞

209. The new vertex
, mentioned in the text, is considered to be vertex n+1, adjacent
to all previous vertices. We put it into the ﬁrst position of every extended frontier;
for example, the extended frontiers (31) become
F0 = (21, 1),
F1 = (21, 2, 5, 17),
F2 = (21, 3, 5, 17, 19),
F19 = (21, 20), with u1 = n + 1
F3 = (21, 4, 5, 17, 19, 6), . . . ,
(cid:7)
and u2 = m + 1. Thus we have
(cid:7)
(cid:7)

(cid:7)

(cid:7)

+

E1

. [Initialize.] Set PATH[m]

←

2, MEM[0][1]

←
1, MEM[1][1]

←
1, WT[1]

←

←

←

←

0 (which is a “bignum”), for 2
0, and FR[k]

IFR[k]

≤
k for 1

←
OMEM[0][j]

←
0 for 0

←

m

≤

≤
k

≤

j < Δ. Also set m
1 (a “bignum”), NBR[0]

≤

n. Set
n. Set
1,

←

1.

←

n + 1, IFR[n + 1]
MEM[1][j]

←

FR[0]
MEM[0][j]
q

←

December 4, 2025

(cid:12)
(cid:12)
(cid:12)
Fischetti
Salvagnin
Ivy League
Patriot League
integer programming
traveling salesrep problem
Gray cycle
plain changes

96

ANSWERS TO EXERCISES

7.2.2.4

←

←

←

←

0’ to ‘FR[1]

The other steps, similarly, have only minor alterations: In answer 187, change ‘FR[0]
m + 1, IFR[m+1]
becomes ‘sortin(k, 1)’. To compute σ and τ , set SIG[0]
SIG[2]
1; SIG[j + 1]
for 2 < j

TAU[1]
q(cid:2). And the ﬁnal paragraph of answer 187 now begins with r

←
1’; also ‘sortin(k, 0)’
0,
j,

TAU[2]
← −
1]] and TAU[SIG[j + 1]]

m + 1, IFR[m+1]

≤
Steps E4
Finally, the cycle test of answer 193 begins by setting MATE[i]

use OMATE[2] instead of OMATE[1].

It does nothing if MATE[1]
k
≥
m + k

0 (that is, if
2 such that either k > q0 or MATE[k]
k(cid:2)
1, and if MATE[k(cid:2)] = 0 for k
−
(We could also make the cycle test update CYC when MATE[1] = 0 (

1.
isn’t inner). Otherwise it ﬁnds the smallest
1] =
0 or FR[k
−
2].
−
is bare).)

1. If FR[k
(cid:0) ] to PATH[m + k

−
q, it adds OWT[p(cid:2)q

1 + IFR[OFR[j

←
1, SIG[1]

MATE[j]

= m + k

and E7

←
←

∞
≥

← −

1]

←

←

←

←

≥

≤

≤

−

−

1.

+

+

210. In the case m = 3, an analogous proof is on page 532 of FGbook.
211. Yale → Harvard → Brown → Columbia → Princeton → Penn → Dartmouth →
Cornell → Yale. (If Penn had beaten Brown, this would’ve been the only such cycle.)
212. False: Consider a

−−→
213. (Solution by M. Fischetti and D. Salvagnin.) A Hamiltonian cycle is impossible
because the 14 teams in the Ivy League plus the Patriot League (Bucknell, Colgate,
Fordham, Holy Cross, Lafayette, Lehigh) dominate only 13 teams (all but Holy Cross).

} −−→ {

x, y, z

a, b, c

a, x

−−→

−−→

−−→

−−→

−−→

x,

y

{

}

z

b

c

.

∞

But here’s a Hamiltonian path, found by integer programming:

Pittsburgh → Louisville → San Jose State → Washington → Arizona State → Baylor → Texas
Tech → Arkansas → Tulsa → New Mexico State → UTEP → Air Force → Hawaii → Brigham
Young → Miami → Syracuse → Michigan State → Rutgers → Boston College → Navy → Akron →
Fullerton → Long Beach → UNLV → Paciﬁc → Utah State → Fresno → Utah → Colorado
State → Oregon → Oregon State → Arizona → UCLA → Stanford → Notre Dame → Colorado →
Oklahoma → Kansas → Oklahoma State → Iowa State → Missouri → Texas Christian → Southern
Methodist → Rice → Houston → Texas A&M → Texas → Penn State → Florida State →
Florida → Mississippi State → Memphis State → Tulane → Louisiana State → Miami of Ohio →
Eastern Michigan → Kent State → Ohio University → Toledo → Western Michigan → Bowling
Green → Cincinnati → West Virginia → Virginia Tech → East Carolina → Temple → Wisconsin →
Ball State → Central Michigan → Kentucky → North Carolina → Maryland → Louisiana Tech →
Southwestern Louisiana → Northern Illinois → Kansas State → New Mexico → San Diego State →
Wyoming → Washington State → California → Southern California → Ohio State → Indiana →
Auburn → Southern Miss → North Carolina State → Georgia Tech → Nebraska → Minnesota →
Iowa → Purdue → Northwestern → Illinois → Michigan → Mississippi → Georgia → Alabama →
Tennessee → Virginia → Clemson → South Carolina → Duke → Wake Forest → Vanderbilt →
Army → Holy Cross → Fordham → Harvard → Cornell → Lafayette → Penn → Dartmouth →
Yale → Brown → Columbia → Princeton → Bucknell → Lehigh → Colgate.

(Integer programming systems have been highly tuned for the traveling salesrep prob-
lem, of which this is a special case. By contrast, Algorithm B is hopelessly ineﬃcient
when given football-tol10.gb; it needs a good way to reject bad partial solutions.)

215. The 145152 solutions are found in 69125228 mems (476.3 mems per cycle).

216. We may assume by symmetry that k = 1. The 2
0α1
an (n

1)-bit Gray cycle. (See Section 7.2.1.1.)

−−→ · · · −−→

0α2

0α2

1α2

−−→

−−→

n−1

n−1

n−1

−−→

−

−

1

1

−

n

-cycles are 0α0
0α0, where (α0 α1 . . . α2

1α0

−−→

−−→

n−1

1α1

−−→
1) is

−

217. The lexicographically smallest of 16 solutions is 1234
−−→
3241
2413
1423
−−→
4213
3124
4312
−−→
1234. (Notice that every other step swaps the middle elements. This is dramatically
diﬀerent from the sequence 7.2.1.2–(3) of “plain changes”!)

1324
3421
3214

1342
4321
2314

1432
4231
2134

−−→
−−→
−−→

−−→
−−→
−−→

−−→
−−→
−−→

2143
4132

2431
3412

1243
4123

2341
3142

−−→
−−→

−−→
−−→

−−→
−−→

−−→
−−→

−−→
−−→

−−→
−−→

December 4, 2025

(cid:12)
7.2.2.4

ANSWERS TO EXERCISES

97

−−→

2134, . . . , 4321

218. (a) Twelve steps 1234
3421 are forced (one for each even
permutation). The other twelve steps are binary choices that form four groups of three:
P1
⇐⇒
2341
−−→
3241; P4
If i

4231
Pj ; otherwise there’s a 4-cycle. (For example,

⇐⇒
−−→
= j we must have Pi

1324
−−→
2143; P3

−−→
⇐⇒
4123

⇐⇒
3142
4321

⇐⇒
−−→
4213

3214
4132.

1243
2431

⇐⇒
−−→

−−→
⇐⇒

2134
3124

⇐⇒
−−→

−−→
⇐⇒

⇐⇒
−−→

1342; P2

⇐⇒
−−→

−−→
3412

2413

1423

1234

4312

2314

3421

1432

−−→

P2 implies 1234

2134

1243

1234.) Hence if, say

¬
P2

−−→
−−→
P4. But then 4321

−−→
3421

−−→
3241

∧

P3
(b) (i) 4144380 cycles, found in 6.7 Gμ; (ii) 6364081880 cycles, found in 6.1 Tμ.

2341

2431

−−→

−−→

−−→

−−→

−−→

−−→

∧

P1 and
P1, we must have
4321.

¬

¬
4231

⇐⇒
∨
2143

Dillon
Farrell
Rodgers
puzzle
de Bruijn cycle
equivalence classes
automorphisms
collinear

220. (a) It appears to be diﬃcult to ﬁnd any of them without computer help. The
lexicographically least is (B00 K22 B11 N33 K41 R30 K32 N21 B02 R20 N23 B04 R40 Q44 K43 Q34
R01 Q03 B13 Q24 K42 N31 R10 Q14 N12 B00); the lexicographically greatest is (B00 Q44 R40 K43
Q34 R01 Q03 N23 K42 N33 Q14 K41 R30 K32 N21 B02 Q24 B13 N31 R10 N12 B04 K22 B11 R20 B00).
(b) Again, solution by hand doesn’t seem easy, although Algorithm B’s search
tree has only 99 nodes: (B00 N44 Q23 R14 N13 B34 Q12 N03 R24 Q04 K40 Q30 K41 B42 R33 B43
K21 B10 N01 K20 N11 R32 K31 R22 Q02 B00). Only Q04

Q30 is forced.

K40

[This exercise was inspired by a puzzle game introduced by D. S. Dillon, J. Farrell,

and T. Rodgers, Homage to a Pied Puzzler (A K Peters, 2009), 125–128.]

Stappers has also constructed examples with pieces
belonging to two players, uppercase and lowercase; in this
variant, each move must capture an opponent’s piece. A nice
two-player puzzle with three pieces of each kind is shown.

n00 q01 B02 b03 K04 k05
N10 q11 q12 N13 B14 N15
K20 R21 k22 R23 K24 Q25
Q30 r31 b32 n33 B34 r35
R40 Q41 r42 n43 k44 b45

221. For example, Algorithm B needs no backtracking to solve this gem:

B00 Q01 R02 B03
K10 K11 K12 K13
N20 N21 N22 N23
N30 N31 N32 N33

.

223. (a) True: x1 . . . xn

−

1xn is preceded by xnx1 . . . xn

1 and x−n x1 . . . xn

1.

−

−

(b) Every Hamiltonian cycle of SB(m, n) corresponds naturally to an m-ary
de Bruijn cycle (see 7.2.1.1–(54)). The correspondence is in fact one-to-one when m = 2.

−−→

−−→

12

11

01

−−→

−−→

(c) 00
(d) (000100201202210211011121222) is lexicographically least, where this nota-
220
122
−−→
x2 . . . xnx1 is in C then x−1 x2 . . . xn
x2 . . . xnx−1 is in C.

−−→
(e) If x1x2 . . . xn
in C, hence x−1 x2 . . . xn

tion means that 000

x2 . . . xnx1 is not

00 is forced.

−−→ · · · −−→

−−→ · · · −−→

1)(m

000.

200

222

001

010

−−→

−−→

−−→

−−→

−−→

−−→

−−→

−−→

1)0

(m

(m

1)

−

−

−

(f) Using Algorithm B we ﬁnd (2, 12, 88, 7510, 675714, 459086712).

(If C is
any cycle, we obtain another by adding 1 to each digit, mod m. We can also go from
x1 . . . xn
¯xn . . . ¯x1. Thus we obtain equivalence classes whose
size is a divisor of 2m. It can be shown that no C has the property that x1x2 . . . xn
+
x2 . . . xnx1
n x
x
x
for example, when m = 4 the cycle

+
−−→
1 . But nontrivial automorphisms do exist;

−−→
+
2 . . . x

y1 . . . yn to ¯yn . . . ¯y1

+
2 . . . x

+
1 x

⇐⇒

−−→

−−→

+
n

−−→
−−→

(0001002003103203313323030130231201212322022132102113110111222333)

is unchanged if we add 2 to each entry, mod 4, then reverse and complement. In this
sense there are 4

7 solutions for m = 4, and 6

56172 for m = 6.)

275 + 12

8 + 8

·

·

·

·

224. Algorithm B proves this when n = 4. But its search tree even in that small case
has 3 million nodes; there’s no evident way to rule out tons of feasible near-solutions.

225. More generally, construct one in SB(m, n) for all m > 3 and n > 2.

227. (i

p)(j(cid:2)

−
−
December 4, 2025

q) > (i(cid:2)

p)(j

−

−

q). (Equality occurs when the three points are collinear.)

(cid:12)
98

ANSWERS TO EXERCISES

7.2.2.4

228. Distances between crossings aren’t preserved under rotation. For example, the
8, 8, 9, 9, 9, 10, 11
north-pointing line has nearly equal distances
, but the distances for
the south-pointing line are
. The distances for lines pointing east
or west are
229. (a) Yes, if and only if m and n are suﬃciently large and at least one of them is
odd. (If m + n is odd, one knight move actually straddles the pivot.)

{
7, 7, 9, 9, 10, 11, 11
}

6, 7, 8, 8, 11, 12, 12

{

}

{

}

.

reﬂection
Beluhov
integer programming problem
cycle covers
90◦ symmetry
Beluhov
Stappers
braids

·

·

·

·

·

·

·

·

·

·

·

·

·

·

1.

−

≥

2m

1+4

2+4

1+4

4, W

5, W

5; W

2; W

4 + 4

2 + 8

17, W

17; W

(5)
6,6 = 2, W

(5)
6,9 = 22 = 2

(7)
7,10 = 48 = 2

(5)
6,10 = 32 = 2

(5)
7,7 = 142 = 2

(3)
3,3 = 1. When m = 6, we have W

(7)
7,8 = 8 = 4
(7)
·
8,9 = 324; and W

(5)
·
7,10 = 20 = 4
10. When m = 8,
(c)
8,10 = (4, 1340, 57784) for c = (5, 6, 7). When m = 9,
(c)
9,10 = (32924, 499220, 3070788) for c = (7, 8, 9).
(c)
·
10,10 = (226436, 5196594, 72217878) for c = (7, 8, 9) (found in
(Incidentally,

(b) The in-degree of (0, 0) is zero when n
(c) Examine carefully the ways that a knight can cross the plumb-line.
(d) To count coils, give the length 1 to arcs that cross the plumb-line, otherwise
length 0; modify Algorithm B so that it reports the total length of each cycle. When
(5)
m < 6 there’s just one solution: W
6,7 =
(5)
7, and
2+4
6,8 = 72 = 2
18 = 2
·
all the tours have 5 coils. When m = 7 the nonzero cases are W
1 + 4
1 + 8
17; W
(7)
8,8 = 1120; W
W
(7)
W
1 + 4
9,9 = 146 = 2
And when m = 10, W
121 Gμ). Examples of highly symmetric tours appear in Fig. A–24.
W
(i(cid:2), j(cid:2)) in answer 227.) The
230. True. (For example, take p = q = 0 and (i, j)
same is true of left-right or top-bottom reﬂection. (Hence, as in the undirected case,
138.)
the 8
231. (Solution by N. Beluhov.) To get c coils, we can set up an integer programming
problem that ﬁnds cycle covers of the digraph — subsets of the arcs for which every
vertex has in-degree 1 and out-degree 1 — together with additional constraints that
force every “ray” from the center to be crossed exactly c times, unless that ray runs
through a vertex. When a short cycle C appears in a solution, add further constraints
to eliminate all cycles that are isomorphic to C. Keep doing this until there are no
more solutions, or time runs out, or a Hamiltonian cycle is found. A solution to (b) for
n = 12, shown in Fig. A–24, was obtained in this way on the 48th trial.

(c)
11,11 = (5936420, 436960600, 23419337498, 12215200) for c = (7, 8, 9, 10).)

8 tours form equivalence classes of sizes 4 and 8; we have 1120 = 4

4 + 8

↔

×

·

·

On the other hand, no cycle covers for (a) were found when n mod 8 = 4 or
n mod 8 = 6; perhaps they do not exist. Several successes with n/2 coils were obtained
18 example with 90◦ symmetry
for n = 16 and n = 18, including the spectacular 18
that appears in Fig. A–24. (In such tours the knight’s polar angle must increase slowly.)
232. (Solution by N. Beluhov and F. Stappers.)
28 is a multiple of 4, it’s
possible to start with a cycle that consists of n disjoint cycles that form n/4 “braids,”
then to stitch them together cleverly while preserving counterclockwise motion. The
32
235. (a) The following constructions are readily generalized to show in fact that
X2m,2n > 0, X2m+1,2m+1 > 0, and X2m+3,2m+4 > 0, for 0 < m

32 example in Fig. A–24 exhibits the general pattern.

If n

n:

×

≥

×

≤

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
7.2.2.4

ANSWERS TO EXERCISES

99

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)Ir

(cid:9)|r

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)C(cid:11)

(cid:9)sr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

Beluhov

(cid:9)I(cid:4)

(cid:9)Cp

(cid:9)|p

(cid:9)|(cid:4)

(cid:9)gp

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)Cp

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I(cid:4)

(cid:9)Cp

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)Cp

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I"

(cid:8)v"

(cid:9)n"

(cid:3)n>

(cid:3)u#

(cid:8)v"

(cid:3)(cid:137)"

(cid:3)n>

(cid:9)u(cid:26)

(cid:3)s(cid:8)

(cid:9)D"

(cid:3)D"

(cid:9)n(cid:28)

(cid:7)n#

(cid:0)(cid:137)"

(cid:9)|(cid:26)

(cid:3)L(cid:8)

(cid:9)D"

(cid:3)C"

(cid:9)n"

(cid:3)n"

(cid:9)L(cid:26)

(cid:3)L(cid:8)

(cid:9)D"

(cid:3)v"

(cid:9)(cid:133)#

Pn"

(cid:3)(cid:137)"

(cid:9)L(cid:26)

(cid:3)L(cid:8)

(cid:9)E"

(cid:8)](cid:4)

(cid:9)(cid:133)(cid:5)

(cid:9)(cid:134)(cid:28)

(cid:9)m=

(cid:3)z=

(cid:9)(cid:136)#

(cid:9)(cid:137)=

(cid:9)(cid:131)M

(cid:3)(cid:130)(cid:8)

(cid:9)G>

(cid:8)(cid:134)#

(cid:3)(cid:137)#

(cid:9)m(cid:5)

(cid:9)(cid:135)=

(cid:9)?[

(cid:3)(cid:130)(cid:8)

(cid:9)E(cid:23)

(cid:8)^F

(cid:9)SU

(cid:9)(cid:133)=

(cid:8)?(cid:26)

(cid:3)A(cid:8)

(cid:9)E(cid:23)

(cid:8)^#

(cid:9)vF

(cid:9)zU

(cid:9)(cid:133)=

(cid:8)?(cid:26)

(cid:3)A(cid:8)

(cid:9)E"

(cid:9)]"

(cid:9);"

(cid:9);=

(cid:3)c#

(cid:9)m#

(cid:3)Z#

(cid:9)Z=

(cid:9)(cid:131)(cid:20)

(cid:9)(cid:130)(cid:8)

(cid:9)D>

(cid:7)^M

(cid:3)j(cid:0)

(cid:9)!=

(cid:7)?[

(cid:3)(cid:130)(cid:8)

(cid:9)G"

(cid:3)^(cid:4)

(cid:3)6=

(cid:9)(cid:136)F

(cid:9)?(cid:26)

(cid:3)L(cid:8)

(cid:9)G"

(cid:3)^(cid:4)

(cid:3)6r

(cid:9)(cid:128)=

(cid:9)(cid:131)F

(cid:9)?(cid:26)

(cid:3)L(cid:8)

(cid:9)D"

(cid:9)v"

(cid:9);(cid:20)

(cid:9);(cid:5)

(cid:9)(cid:134)=

(cid:9)(cid:136)#

(cid:9)Z"

(cid:9)Z"

(cid:9)u(cid:26)

(cid:9)L(cid:8)

(cid:9)D(cid:26)

(cid:3)^r

(cid:9)(cid:134)r

(cid:9)q}

(cid:9)(cid:138)>

(cid:3)(cid:135)(cid:26)

(cid:3)A(cid:8)

(cid:9)E=

(cid:8)EU

(cid:9)(cid:22)"

(cid:8)(cid:22)=

(cid:9){[

(cid:3)(cid:130)(cid:8)

(cid:9)E=

(cid:8)E#

(cid:9)(cid:138)"

(cid:3)(cid:22)(cid:4)

(cid:0)6=

(cid:9)(cid:131)[

(cid:3)(cid:130)(cid:8)

(cid:9)D#

(cid:7)vr

(cid:9)q(cid:26)

(cid:9)(cid:25)>

(cid:9)(cid:128)(cid:5)

(cid:3)q(cid:4)

(cid:9)(cid:10)"

(cid:9)(cid:18)"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)_"

(cid:9)ǱR

(cid:9){"

(cid:9)1R

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)ǱR

(cid:9){#

(cid:9)1"

(cid:9)ǱR

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_#

(cid:7)Ǳ>

(cid:9)(cid:22)#

(cid:8)(cid:138)=

(cid:3)(cid:131)>

(cid:8)]>

(cid:8)(cid:22)"

(cid:8)(cid:22)F

(cid:9){$

(cid:3)b(cid:8)

(cid:9)E#

(cid:8)Ǳ}

(cid:9)(cid:138)>

(cid:0)(cid:22)(cid:4)

(cid:8)(cid:22)>

(cid:9)(cid:130)[

(cid:3)(cid:130)(cid:8)

(cid:9)_"

(cid:9)Ǳ#

(cid:9)1#

(cid:9)Ǳ"

(cid:9)ǱR

(cid:9){.

(cid:9)b(cid:8)

(cid:9)_#

(cid:9)Ǳ=

(cid:9)_F

(cid:9)a#

(cid:9)1#

(cid:9)ǱF

(cid:9)a"

(cid:9)bF

(cid:9){.

(cid:9)b(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)C(cid:4)

(cid:9)C(cid:4)

(cid:9)gr

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)C(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)D"

(cid:3)I"

(cid:9)(cid:133)"

(cid:2)n"

(cid:3)n"

(cid:9)n"

(cid:9)(cid:133)#

Pn"

(cid:3)(cid:137)"

(cid:9)n"

(cid:9)L(cid:26)

(cid:3)L(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)gp

(cid:9)|p

(cid:9)|(cid:4)

(cid:9)gp

(cid:9)|(cid:11)

(cid:9)sp

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)G>

(cid:8)^R

(cid:3)iR

(cid:9)c(cid:4)

(cid:9)(cid:133)(cid:4)

(cid:9)C#

(cid:9)(cid:137)R

(cid:9)zr

(cid:9)u2

(cid:9)g=

(cid:8)?(cid:26)

(cid:3)A(cid:8)

(cid:9)D"

(cid:3)D"

(cid:3)n"

(cid:9)n(cid:28)

(cid:3)n#

(cid:3)v"

(cid:9)v#

(cid:7)n>

(cid:9)|(cid:26)

(cid:3)s(cid:8)

(cid:9)~(cid:12)

(cid:0)^(cid:26)

(cid:9)^(cid:4)

(cid:9)I#

(cid:9)v"

(cid:3)g"

(cid:9)(cid:133)#

(cid:9)n>

(cid:9)|=

(cid:3)(cid:136)R

(cid:9)?(cid:26)

(cid:3)L(cid:8)

(cid:9)I>

(cid:8)^[

(cid:3)j(cid:4)

(cid:9)I2

(cid:9)f(cid:29)

(cid:8)(cid:135)=

(cid:3)k#

(cid:9)m=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G"

(cid:3)^(cid:5)

(cid:3)w(cid:28)

(cid:9)vR

(cid:3)i(cid:4)

(cid:9)(cid:133)"

(cid:9)v"

(cid:9)L>

(cid:9)u(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)D"

(cid:3)](cid:19)

(cid:9)o>

(cid:9)CR

(cid:8)iR

(cid:9)c(cid:11)

(cid:7)L(cid:26)

(cid:9)s=

(cid:9)?[

(cid:3)(cid:130)(cid:8)

(cid:9)G=

(cid:3)S}

(cid:9)D=

(cid:3)G(cid:4)

(cid:9)]U

(cid:9)I"

(cid:8)|(cid:26)

(cid:3)L=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:4)

(cid:8)]"

(cid:9)(cid:137)(cid:26)

(cid:3)<"

(cid:9)^#

(cid:9)n2

(cid:3)f#

(cid:8)-=

(cid:9)?[

(cid:3)(cid:130)(cid:8)

(cid:9)E(cid:12)

(cid:8)^=

(cid:9)S>

(cid:3)]#

(cid:8)vF

(cid:9)ER

P{M

(cid:3)Q=

(cid:9)(cid:136)(cid:26)

(cid:3)A=

(cid:9)(cid:136)(cid:26)

(cid:3)A(cid:8)

(cid:9)D(cid:11)

(cid:7)^R

(cid:9)i(cid:29)

(cid:7)w(cid:4)

(cid:3)(cid:22)=

(cid:9)?=

(cid:9)d"

(cid:8)(cid:138)>

(cid:9)u(cid:26)

(cid:3)A(cid:8)

(cid:9)G"

(cid:3)^(cid:4)

(cid:3)6(cid:29)

(cid:9)(cid:134)"

(cid:3)^#

(cid:9)1F

(cid:9)a(cid:29)

(cid:9)b=

(cid:3)(cid:131)2

(cid:3)f=

(cid:8)?(cid:26)

(cid:3)A(cid:8)

(cid:9)D(cid:26)

(cid:3)^=

(cid:9)_=

(cid:9)E(cid:4)

(cid:8)(cid:18)"

(cid:9)-=

(cid:3){"

(cid:9)(cid:10)>

(cid:9)u[

(cid:3)(cid:130)(cid:8)

(cid:9)E=

(cid:8)S(cid:26)

(cid:9)(cid:25)R

(cid:9)E(cid:4)

(cid:0)6(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)=

(cid:9)(cid:131)=

(cid:9)(cid:131)=

(cid:9)(cid:131)R

(cid:9)?(cid:26)

(cid:3)L(cid:8)

(cid:9)G(cid:11)

(cid:8)^p

(cid:9)q(cid:29)

(cid:9)(cid:25)"

(cid:3)(cid:134)"

(cid:3)w.

(cid:9)b(cid:28)

(cid:9)!F

(cid:3)?$

(cid:3)b(cid:8)

(cid:9)_"

(cid:3)^(cid:26)

(cid:3)<=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1#

(cid:9)1(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:18)=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)_#

(cid:7)Ǳ>

(cid:9)(cid:22)=

(cid:8)(cid:131)=

(cid:9)(cid:131)>

(cid:8)(cid:22)(cid:4)

(cid:8)(cid:22)>

(cid:9)(cid:22)>

(cid:8)(cid:130)[

(cid:3)(cid:130)(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)gp

(cid:9)Jp

(cid:9)|p

(cid:9)|(cid:4)

(cid:9)gp

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)D"

(cid:3)I"

(cid:9)n"

(cid:3)n(cid:28)

(cid:3)n(cid:28)

(cid:7)v#

(cid:0)(cid:137)"

(cid:9)s(cid:26)

(cid:3)L(cid:8)

(cid:9)G>

(cid:8)(cid:134)F

(cid:3)i(cid:4)

(cid:9)(cid:133)#

(cid:9)m#

(cid:3)mU

(cid:9)f=

(cid:8)?(cid:26)

(cid:3)A(cid:8)

(cid:9)D>

(cid:7)](cid:19)

(cid:8)j(cid:4)

(cid:9)CR

(cid:9)S(cid:26)

(cid:9)L=

(cid:9)(cid:136)F

(cid:9)?[

(cid:3)Q(cid:8)

(cid:9)D(cid:11)

(cid:7)^"

(cid:9)jU

(cid:3)6"

(cid:3)(cid:133)#

(cid:8)!=

(cid:9)?[

(cid:3)(cid:130)(cid:8)

(cid:9)~(cid:23)

(cid:0)^=

(cid:9)S=

(cid:9)EF

(cid:9)(cid:136)=

(cid:9){"

(cid:9)!>

(cid:7)u[

(cid:3)(cid:130)(cid:8)

(cid:9)G"

(cid:3)^r

(cid:7)w(cid:29)

(cid:9)q"

(cid:3)q(cid:4)

(cid:9)6}

(cid:9)->

(cid:3)(cid:135)(cid:26)

(cid:3)A(cid:8)

(cid:9)E=

(cid:8)_}

(cid:9)(cid:138)=

(cid:0)(cid:131)>

(cid:8)(cid:22)U

(cid:8)(cid:22)"

(cid:8)(cid:22)>

(cid:9)b[

(cid:3)(cid:130)(cid:8)

(cid:9)E=

(cid:8)E(cid:4)

(cid:8)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)>

(cid:9)(cid:22)"

(cid:8)(cid:22)F

(cid:9){$

(cid:3)b(cid:8)

(cid:9)_#

(cid:9)Ǳ=

(cid:9)_"

(cid:9)_R

(cid:9)_"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1F

(cid:9){"

(cid:9)bF

(cid:9){.

(cid:9)b(cid:8)

(cid:9)Ǳ#

(cid:9)1#

(cid:9)Ǳ"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)b.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)Ǳ#

(cid:9)1#

(cid:9)Ǳ#

(cid:9)ǱR

(cid:9)a"

(cid:9)1R

(cid:9){.

(cid:9)b(cid:8)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)I(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:5)

(cid:9)J(cid:5)

(cid:9)Jr

(cid:9)J(cid:5)

(cid:9)|r

(cid:9)J(cid:4)

(cid:9)gr

(cid:9)|(cid:11)

(cid:9)s(cid:4)

(cid:9)g(cid:11)

(cid:9)s(cid:11)

(cid:9)s(cid:26)

(cid:9)s(cid:8)

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)L(cid:8)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s(cid:8)

(cid:9)I"

(cid:8)C"

(cid:0)n"

(cid:3)n"

(cid:3)(cid:133)"

(cid:9)u"

(cid:3)u(cid:28)

(cid:3)n>

(cid:3)J(cid:28)

(cid:8)v}

(cid:3)(cid:137)#

(cid:3)v"

(cid:9)v#

(cid:7)n#

(cid:9)(cid:137)"

(cid:3)(cid:137)(cid:29)

(cid:7)L(cid:26)

(cid:3)s(cid:8)

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)L=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)I"

(cid:8)(cid:134)"

(cid:9)o.

(cid:9)o(cid:5)

(cid:9)(cid:134)R

(cid:9)S=

(cid:3)c=

(cid:3)z(cid:28)

(cid:3)m=

(cid:3)z(cid:29)

(cid:9)(cid:135)U

(cid:3)f=

(cid:8)k#

(cid:9)m=

(cid:9)(cid:136)=

(cid:9)k=

(cid:7)?(cid:26)

(cid:3)s(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)L=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G"

(cid:3)(cid:134)(cid:4)

(cid:3)(cid:133)(cid:4)

(cid:9)I>

(cid:9)I(cid:4)

(cid:8)I(cid:5)

(cid:9)(cid:135)=

(cid:9)z=

(cid:9)S(cid:5)

(cid:9)(cid:135)=

(cid:9)S=

(cid:8)i"

(cid:9)s(cid:29)

(cid:9)L(cid:26)

(cid:3)s=

(cid:9)k=

(cid:9)?(cid:26)

(cid:3)s(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)L=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)I>

(cid:8)^M

(cid:3)j"

(cid:9)CR

(cid:0)c"

(cid:3)o"

(cid:3)(cid:133)(cid:29)

Pu(cid:5)

(cid:3)J(cid:28)

(cid:9)v#

(cid:3)v(cid:29)

(cid:9)A#

(cid:3)(cid:137)=

(cid:7)d(cid:11)

(cid:8)s#

(cid:9)(cid:137)=

(cid:9)(cid:136)(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)D"

(cid:3)](cid:29)

(cid:9)o(cid:4)

(cid:3)I"

(cid:9)(cid:134).

(cid:9)o(cid:5)

(cid:9)(cid:134)R

(cid:9)z>

(cid:3)u=

(cid:3)S#

(cid:3)m=

(cid:3)(cid:136)=

(cid:9)k=

(cid:9)k"

(cid:3)s2

(cid:9)(cid:133)=

(cid:8)(cid:131)(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)|(cid:4)

(cid:9)g(cid:4)

(cid:9)gr

(cid:9)|(cid:26)

(cid:9)s=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)u(cid:26)

(cid:3)L=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:4)

(cid:8)]F

(cid:9)i>

(cid:9)w"

(cid:3)g(cid:4)

(cid:0)(cid:133)>

(cid:9)I=

(cid:8)G=

(cid:9)z=

(cid:3)z=

(cid:9)(cid:136)(cid:11)

(cid:8)s#

(cid:9)(cid:137)=

(cid:9)(cid:136)#

(cid:3)(cid:138)=

(cid:9)dF

(cid:9)(cid:131)(cid:20)

(cid:3)Q(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n"

(cid:9)n#

(cid:7)n"

(cid:9)(cid:137)"

(cid:9)u(cid:26)

(cid:3)L=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)I(cid:4)

(cid:9)C(cid:4)

(cid:9)g(cid:4)

(cid:9)g(cid:4)

(cid:9)g#

(cid:9)(cid:137)r

(cid:9)(cid:135)(cid:26)

(cid:9)s=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)~p

P(cid:134)"

(cid:9)(cid:137)>

(cid:9)6(cid:4)

(cid:8)]"

(cid:9)j"

(cid:9)(cid:133)"

(cid:0)o=

(cid:3)c#

(cid:9)m=

(cid:7)k(cid:4)

(cid:3)g#

(cid:9)Z=

(cid:2)(cid:131)#

(cid:9)Z#

(cid:9)ZR

(cid:9)?(cid:20)

(cid:9)Q(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)D"

(cid:3)v"

(cid:9)n"

(cid:9)n"

(cid:9)u"

(cid:9)n>

(cid:9)u(cid:26)

(cid:3)s=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^(cid:4)

(cid:9)Ir

(cid:9)J>

(cid:9)|#

(cid:3)(cid:137)=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)D"

(cid:9)](cid:11)

(cid:0);#

(cid:9)(cid:137)"

(cid:9)]"

(cid:9)6(cid:11)

(cid:9);"

(cid:9)j.

(cid:9)o=

(cid:9)k=

(cid:9)d#

(cid:9)ZF

(cid:9)(cid:131)"

(cid:9)Q(cid:4)

(cid:9)(cid:133)"

(cid:9)!"

(cid:9)QM

(cid:3)Q(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^}

(cid:9)D"

(cid:3)v>

(cid:7)LM

(cid:3)(cid:130)=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)~#

(cid:0)~"

(cid:9)j(cid:4)

(cid:9)6#

(cid:9)~"

(cid:9)v"

(cid:9);(cid:11)

(cid:9)<(cid:26)

(cid:9)(cid:25)(cid:4)

(cid:9)(cid:10)#

(cid:9)!"

(cid:9)Z"

(cid:9)(cid:133)p

(cid:9)u#

(cid:9)(cid:138)"

(cid:9)Zp

Pu(cid:20)

(cid:9)(cid:130)(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)_F

(cid:9)aU

(cid:9)6(cid:4)

(cid:8)(cid:22)=

(cid:9)(cid:136)(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)E#

(cid:8)Ǳ(cid:20)

(cid:3)(cid:130)(cid:26)

(cid:9)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)~"

(cid:9)^"

(cid:9);(cid:20)

(cid:9);"

(cid:9)v"

(cid:3);#

(cid:9)1(cid:29)

:(cid:25)(cid:5)

(cid:3)q>

(cid:9)(cid:18)"

(cid:8)(cid:10)(cid:4)

(cid:0)6"

(cid:9)!"

(cid:9)u(cid:4)

(cid:7)(cid:133)#

(cid:9)(cid:138)"

(cid:9)(cid:135)M

(cid:3)Q(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1(cid:4)

(cid:9)6=

(cid:9)(cid:136)R

(cid:9)(cid:131)(cid:4)

(cid:9)6=

(cid:9)(cid:131)(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)=

(cid:9)(cid:131)"

(cid:9)(cid:22)R

(cid:2){T

(cid:3)b=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)~"

(cid:0)v(cid:11)

(cid:9)<#

(cid:9)(cid:137)=

(cid:7)S#

(cid:9)(cid:138)=

(cid:9)_=

(cid:3)S>

(cid:9)(cid:128)(cid:5)

(cid:3)(cid:128)"

(cid:9)A"

(cid:3)b"

(cid:9)6(cid:28)

(cid:0)1(cid:4)

(cid:3)f"

(cid:9)->

(cid:9)u(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)"

(cid:3)(cid:22)#

(cid:9)1(cid:4)

(cid:9)(cid:22)R

(cid:9)(cid:131)T

(cid:3)b=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1F

(cid:9){#

(cid:9)1"

(cid:9)(cid:138)(cid:4)

(cid:9)6R

(cid:9)(cid:131)(cid:4)

(cid:9)6=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G"

(cid:3)v(cid:4)

(cid:3)6=

(cid:9)_(cid:11)

(cid:0)(cid:25)(cid:26)

(cid:9)(cid:25)=

(cid:9)S(cid:29)

(cid:3)q=

(cid:3)(cid:136)>

(cid:3)](cid:5)

(cid:8)(cid:128)(cid:5)

(cid:9)(cid:135)(cid:4)

(cid:9)(cid:10)"

(cid:9)(cid:135)(cid:29)

(cid:9)b"

(cid:3)(cid:10)>

(cid:9)uM

(cid:3)(cid:130)(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:22)"

(cid:9)(cid:22)(cid:4)

(cid:9)6F

(cid:9)(cid:131)$

(cid:3)b=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1#

(cid:9)1"

(cid:9)(cid:138)(cid:4)

(cid:9)6"

(cid:9)(cid:138)"

(cid:9)6F

(cid:9){.

(cid:9)b=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G=

(cid:8)S#

(cid:9)(cid:138)F

(cid:9)_(cid:29)

(cid:7)<#

(cid:3)(cid:138)=

(cid:7)G=

(cid:9)(cid:131)=

(cid:3)(cid:131)=

(cid:9)a"

(cid:3)]>

(cid:0)6>

(cid:8)(cid:10)"

(cid:8)(cid:18)=

(cid:0){}

(cid:9)!R

(cid:3)?$

(cid:3)b(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:22)"

(cid:9)(cid:22)(cid:4)

(cid:9)6"

(cid:9)(cid:22)(cid:4)

(cid:9)6=

(cid:9)(cid:131)M

(cid:3)(cid:130)=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)_(cid:11)

(cid:7)^(cid:26)

(cid:9)(cid:25)=

(cid:9)_=

(cid:3)E=

(cid:9)_(cid:28)

(cid:9)-=

(cid:3)(cid:136)(cid:5)

(cid:9)(cid:134)=

(cid:9)(cid:136)(cid:5)

(cid:9)(cid:128)"

(cid:9)(cid:134)"

(cid:9)b"

(cid:3)b"

(cid:9)b>

(cid:9)6>

(cid:8)(cid:135)(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:22)"

(cid:9)(cid:22)(cid:4)

(cid:9)6"

(cid:9)(cid:22)(cid:4)

(cid:9)6(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)=

(cid:9)(cid:131)M

(cid:3)(cid:130)=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1#

(cid:9)1"

(cid:9)(cid:138)(cid:4)

(cid:9)6"

(cid:9)(cid:138)"

(cid:9)6"

(cid:9)1"

(cid:9)1F

(cid:9){.

(cid:9)b=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)_(cid:29)

(cid:7)^(cid:26)

(cid:3)(cid:25)=

(cid:9)Sr

(cid:9)q"

(cid:9)(cid:25)(cid:29)

(cid:3)w(cid:5)

(cid:3)(cid:134)>

(cid:9)(cid:128)(cid:29)

(cid:3)q>

(cid:3)(cid:128)>

(cid:3)(cid:18)=

(cid:8)(cid:136)(cid:5)

(cid:9)(cid:135)(cid:4)

(cid:9)(cid:10)(cid:4)

(cid:9)(cid:10)"

(cid:9)(cid:135)$

(cid:3)b(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1#

(cid:9)1"

(cid:9)(cid:138)(cid:4)

(cid:9)6"

(cid:9)(cid:138)"

(cid:9)6"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1F

(cid:9){.

(cid:9)b=

(cid:9)?(cid:26)

(cid:3)A=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:22)#

(cid:9)(cid:138)(cid:4)

(cid:9)(cid:18)"

(cid:9)q(cid:4)

(cid:9)6"

(cid:9)(cid:22)(cid:4)

(cid:9)6(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)=

(cid:9)(cid:131)M

(cid:3)(cid:130)=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)_=

(cid:7)E#

(cid:8)(cid:138)#

(cid:2)(cid:138)>

(cid:9)(cid:22)=

(cid:8)(cid:131)=

(cid:9)(cid:131)(cid:28)

(cid:8)(cid:138)=

(cid:3)(cid:131)=

(cid:8)a>

(cid:3)(cid:22)U

(cid:8)]"

(cid:8)]>

(cid:9)6>

(cid:8)(cid:22)"

(cid:8)(cid:22)R

(cid:0){$

(cid:3)b(cid:8)

(cid:9)G(cid:26)

(cid:3)^=

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1(cid:4)

(cid:9)6"

(cid:9)-(cid:5)

(cid:3)w"

(cid:9)-p

(cid:7)w"

(cid:9)(cid:138)"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1F

(cid:9){.

(cid:9)b=

(cid:9)?(cid:26)

(cid:3)A(cid:8)

(cid:9)E(cid:4)

(cid:8)](cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)2

(cid:9)(cid:22)F

(cid:8)(cid:131)>

(cid:9)6#

(cid:8)(cid:138)>

(cid:9)](cid:4)

(cid:8)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)(cid:4)

(cid:9)(cid:22)=

(cid:9)(cid:131)M

(cid:3)(cid:130)(cid:8)

(cid:9)_=

(cid:9)_R

(cid:9)_#

(cid:9)1=

(cid:9)_"

(cid:9)Ǳ#

(cid:9)1=

(cid:9)a#

(cid:9)Ǳ=

(cid:9)a=

(cid:9)aF

(cid:9)a"

(cid:9)1"

(cid:9)1"

(cid:9)b"

(cid:9)b"

(cid:9)b.

(cid:9)b(cid:8)

(cid:9)_"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1F

(cid:9){"

(cid:9)1=

(cid:9){"

(cid:9)Ǳ#

(cid:9)1"

(cid:9)Ǳ"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1"

(cid:9)1F

(cid:9){.

(cid:9)b(cid:8)

Fig. A–24. A gallery of whirling knight’s tours with special qualities.

(b) (Solution by N. Beluhov.) Assume that m

pass through exactly one of the vertices
If n is odd, every coil must pass through exactly one of
hence c =
−

n. If m is odd, every coil must
1
−
.
2 < k < n
}
(cid:17)
1
−
;
2 )
(k,
}
. When both are even, every coil must pass through exactly one of
0

; hence c =
k <

; hence c = m/2.

n/2
(cid:16)
1
m
−
2

m+n
2

k <

, k)

(k,

m
2

≤
n

≤

−
2

{

0

{

m

(

n

|

|

1

m/2
(cid:17)
k)
|

(cid:16)
2
−

≤

}

, because the plumb-line can be crossed only from

(c) This is a consequence of (b): If n is odd, we must have m = n. Otherwise c =
n
m+1
2 .
vertices in column
2
(d) Let m be even. Every whirling king’s tour must include the arcs v(k, j)
j <

−−→
k, where v(k, j) =

k < m/2 and 0

(0, 1) for 0

m+1
2

m/2

n/2

1

{
n
2

≤

≤

(cid:16)

(cid:17) −

−

−

v(k, j)

−
December 4, 2025

≤

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:26)
$
%
&
’
(
)
*
+
,
(cid:0)
(cid:7)
#
(cid:29)
(cid:19)
.
3
(cid:14)
8
)

(cid:16)
(cid:24)
(cid:2)
#
7
&
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:26)
.
&
3
(cid:13)
/
K

0
(cid:7)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
(cid:14)
e
9
(cid:24)
,
(cid:0)
(cid:26)
(cid:13)
)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
.
3
8

(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
%
H
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
(cid:30)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
7
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
(cid:30)
K

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:4)
(cid:19)
(cid:20)
%
x
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
.
3
(cid:14)
8
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
’
(
)
*
+
,
(cid:0)
(cid:7)
>
(cid:4)
.
&
/
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
4
W
X
#
(cid:20)
%
&
O
(
)
+
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:26)
.
&
3
(cid:13)
/
K

0
(cid:7)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
(cid:14)
e
9
(cid:24)
,
(cid:0)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
3
8

(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
%
H
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
(cid:30)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
7
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
(cid:30)
K

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
%
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:4)
(cid:20)
%
&
O
(
V
\
:
(cid:0)
(cid:2)
(cid:11)
(cid:19)
$
.
N
(cid:14)
8
(cid:15)
e
(cid:17)
P
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:5)
$
%
&
(cid:6)
N
(
)
*
+
,
(cid:7)
}
.
&
/
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
$
.
&
N
t
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
(cid:11)
M
&
N
O
(
(cid:15)
*
0
5
P
>
(cid:29)
(cid:5)
(cid:20)
&
(cid:30)
O
(
K

0
(cid:2)
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
$
@
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
M
N
O
*
P
(cid:0)
(cid:8)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
r
H
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
l
(cid:129)
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
}
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
p
$
&
(cid:6)
N
(
(cid:31)
(cid:15)
*
0
5
P
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
‘
’
(
*
+
,
(cid:0)
(cid:7)
@
(cid:6)
(cid:15)
5
(cid:2)
(cid:7)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
O
(cid:31)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:5)
$
‘
(cid:6)
N
(
(cid:31)
*
0
P
(cid:7)
$
@
’
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:11)
(cid:20)
&
O
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:4)
(cid:11)
[
&
N
O
(
(cid:31)
(cid:15)
*
0
5
P
(cid:11)
(cid:19)
M
N
x
(cid:15)
e
(cid:17)
P
(cid:0)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
@
3
(cid:21)
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
p
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:23)
$
%
(cid:129)
(cid:14)
)
e
9
(cid:24)
,
(cid:0)
}
.
&
/
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:28)
$
.
&
N
t
V
*
0
P
(cid:0)
(cid:7)
(cid:5)
$
.
&
(cid:6)
N
/
(cid:31)
*
0
P
(cid:7)
(cid:29)
(cid:11)
(cid:26)
$
3
(cid:129)
h
*
5
P
(cid:7)
#
(cid:29)
(cid:20)
%
&
3
O
(
)

\
:
(cid:2)
#
7
&
t
)
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:29)
r
.
&
H
/
(cid:31)
h
0
5
(cid:2)
(cid:7)
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
$
%
@
N
(cid:14)
)
W
9
(cid:24)
Y
(cid:0)
(cid:19)
.
(cid:14)
8
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:19)
@
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:29)
@
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
‘
N
(
*
+
,
(cid:0)
(cid:7)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:20)
&
3
O
(
(cid:31)
4
0
5
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
@
(cid:14)
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
.
x
8
)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
>
(cid:20)
.
O
8
K
(cid:0)
(cid:2)
(cid:3)
$
.
N
8
*
P
(cid:0)
(cid:7)
(cid:29)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
%
&
(
+
:
(cid:0)
(cid:2)
(cid:7)
(cid:4)
(cid:11)
(cid:19)
&
(cid:14)
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
&
x
(
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:2)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:26)
&
(cid:13)
(
)
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:11)
(cid:20)
.
&
O
t
)
(cid:15)
0
5
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:4)
(cid:19)
&
(cid:14)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
(cid:5)
(cid:19)
.
&
(cid:6)
(cid:14)
t
)
(cid:16)
0
(cid:24)
(cid:2)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
%
&
(cid:129)
(
(cid:15)
*
\
5
Y
(cid:0)
(cid:20)
&
(cid:6)
O
(
(cid:15)
0
5
(cid:2)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:29)
r
(cid:26)
H
(cid:13)
(cid:31)
h
5
(cid:7)
(cid:8)
[
%
(cid:6)
N
O
*
9
,
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:23)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
(cid:19)
.
H
(cid:14)
8
V

(cid:16)
(cid:24)
(cid:2)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
%
‘
N
(
(cid:15)
*
+
5
,
(cid:0)
2
(cid:11)
(cid:20)
&
3
O
(
(cid:31)
4
0
5
(cid:2)
(cid:29)
(cid:11)
(cid:19)
[
%
3
N
(cid:21)
4
W
9
X
,
>
(cid:20)
%
&
O
(
(cid:31)
+
:
(cid:0)
(cid:2)
(cid:4)
(cid:11)
$
@
N
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
2
(cid:11)
(cid:19)
[
3
N
(cid:21)
(cid:31)
4
W
X
P
(cid:4)
(cid:19)
[
%
N
(cid:21)
)
W
9
(cid:24)
,
(cid:0)
>
(cid:29)
(cid:19)
.
3
(cid:14)
8
K

(cid:16)
(cid:24)
(cid:2)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:5)
$
%
&
(cid:6)
N
(
)
*
\
Y
(cid:7)
2
(cid:19)
.
3
(cid:14)
8
)

(cid:16)
(cid:24)
(cid:2)
#
(cid:29)
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
#
T
&
/
)
\
:
(cid:0)
(cid:2)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:4)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
h
e
(cid:17)
#
(cid:20)
%
&
O
(
)
\
:
(cid:0)
(cid:2)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:26)
.
&
3
(cid:13)
t
V

0
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
@
’
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:7)
[
N
O
)
*
P
(cid:0)
(cid:8)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
(cid:6)
8
(cid:15)
5
(cid:2)
(cid:7)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
%
(cid:30)
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
l
’
(cid:14)
(
W
\
(cid:24)
Y
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:12)
3
(cid:13)
(cid:14)
h
(cid:16)
(cid:17)
(cid:8)
(cid:4)
(cid:20)
%
&
O
(
)
\
:
(cid:0)
(cid:2)
(cid:4)
(cid:19)
.
(cid:14)
8
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:5)
(cid:20)
&
(cid:6)
O
(
(cid:31)
0
(cid:2)
(cid:3)
(cid:26)
$
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
T
(cid:6)
8
9
:
(cid:2)
(cid:7)
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
(cid:31)
h
5
(cid:7)
(cid:8)
[
%
&
N
O
(
)
*
+
,
(cid:0)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:23)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:26)
.
&
(cid:13)
/
)
0
(cid:0)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
.
H
8
(cid:31)

(cid:2)
(cid:7)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
$
%
&
(cid:6)
N
(
*
\
Y
(cid:7)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
H
(cid:14)
h
(cid:16)
X
(cid:2)
(cid:8)
(cid:29)
(cid:5)
(cid:19)
(cid:20)
%
(cid:30)
x
)

(cid:16)
9
(cid:24)
:
(cid:2)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
’
(cid:14)
W
9
(cid:24)
Y
(cid:0)
>
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
$
@
N
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:23)
$
(cid:129)
(cid:14)
e
(cid:24)
P
(cid:0)
>
(cid:4)
&
(
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:11)
(cid:19)
$
.
3
N
(cid:14)
8
V
4
W
X
7
N
O
8
*
9
Y
(cid:0)
>
(cid:29)
(cid:26)
3
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:26)
3
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
T
8
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:5)
(cid:19)
@
(cid:30)
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:26)
%
@
(cid:13)
)
9
:
(cid:0)
(cid:7)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
.
@
3
8
h
5
(cid:2)
(cid:7)
(cid:29)
(cid:20)
%
3
O

9
:
(cid:2)
(cid:8)
%
@
3

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
(cid:19)
%
(cid:30)
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
$
%
’
(cid:14)
(cid:15)
W
9
(cid:17)
Y
(cid:0)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
U
3
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
7
N
(cid:14)
8
(cid:15)
W
9
X
Y
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
l
3
(cid:13)
(
)

\
:
(cid:7)
7
(cid:13)
8
9
:
(cid:0)
(cid:7)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
&
(cid:6)
(
0
(cid:2)
(cid:7)
(cid:3)
(cid:23)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
U
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
U
(cid:11)
(cid:19)
%
3
(cid:14)
h
(cid:16)
9
(cid:17)
:
(cid:2)
(cid:11)
(cid:19)
(cid:20)
%
x
(cid:15)
(cid:16)
9
X
:
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
2
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:4)
(cid:19)
[
%
N
(cid:21)
)
W
9
(cid:24)
,
(cid:0)
>
(cid:29)
(cid:19)
.
3
(cid:14)
8
K

(cid:16)
(cid:24)
(cid:2)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:5)
$
&
(cid:6)
N
(
V
*
0
P
(cid:7)
#
$
.
&
N
/
)
*
0
P
(cid:0)
(cid:7)
}
.
&
/
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
$
.
&
N
t
(cid:31)
*
0
P
(cid:0)
(cid:7)
(cid:26)
$
&
(cid:129)
(
*
0
P
(cid:0)
(cid:7)
}
(cid:29)
(cid:26)
&
3
(cid:13)
(
K

0
(cid:7)
(cid:3)
(cid:11)
$
7
&
N
t
(cid:15)
*
+
5
Y
(cid:0)
(cid:29)
p
(cid:20)
&
(cid:30)
O
(
(cid:31)
4
0
5
(cid:2)
M
%
’
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
$
@
(cid:129)
(cid:14)
(cid:31)
(cid:15)
e
X
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
@
3
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
%
@
(cid:30)
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
#
%
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
&
(cid:30)
(
(cid:31)

0
(cid:2)
(cid:7)
(cid:3)
$
%
@
’
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
$
%
‘
N
(
)
*
+
,
(cid:0)
(cid:7)
.
@
(cid:14)
8
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:4)
(cid:11)
(cid:26)
(cid:13)
(cid:31)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:19)
[
N
(cid:21)
)
W
(cid:24)
P
(cid:0)
>
.
8
V
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:26)
$
.
’
8
(cid:15)
*
5
P
(cid:0)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
r
H
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:8)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
@
N
(cid:15)
*
5
P
(cid:0)
(cid:7)
#
(cid:29)
(cid:19)
(cid:20)
3
x
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
T
&
(cid:13)
/
\
:
(cid:0)
(cid:7)
(cid:26)
@
(cid:13)
)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
.
3
8

(cid:2)
(cid:7)
(cid:3)
%
l
3
(

\
:
(cid:2)
(cid:7)
(cid:12)
%
(cid:13)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
>
p
&
(cid:6)
(
(cid:31)
(cid:15)
0
5
(cid:2)
(cid:7)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
l
(cid:129)
(
(cid:15)
*
0
5
P
(cid:0)
(cid:29)
(cid:20)
3
O
)

(cid:2)
(cid:8)
(cid:3)
p
T
(cid:30)
8
4
9
5
:
(cid:2)
(cid:20)
%
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
2
(cid:11)
3
4
5
(cid:2)
(cid:7)
(cid:8)
#
(cid:19)
(cid:20)
%
(cid:21)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:5)
.
&
(cid:6)
t
(cid:31)
0
(cid:2)
(cid:7)
(cid:3)
$
@
’
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
‘
’
(
*
+
,
(cid:0)
(cid:7)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
&
(
(cid:31)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:12)
$
’
(cid:14)
W
(cid:24)
P
(cid:0)
(cid:28)
(cid:12)
(cid:13)
(cid:14)
V
(cid:16)
(cid:24)
(cid:0)
(cid:8)
$
.
&
N
/
*
0
P
(cid:0)
(cid:7)
(cid:4)
(cid:5)
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
r
(cid:19)
.
H
(cid:14)
8
(cid:31)
h
(cid:16)
X
(cid:2)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
@
’
(cid:15)
*
9
5
,
(cid:0)
(cid:7)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:26)
(cid:20)
3
(cid:13)
O

(cid:8)
(cid:3)
(cid:29)
(cid:5)
%
@
H
)

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:5)
T
(cid:6)
8
)
9
:
(cid:2)
(cid:7)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
$
&
(cid:6)
N
(
K
*
0
P
(cid:7)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
}
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
%
l
N
(
(cid:15)
*
\
5
Y
(cid:0)
U
(cid:11)
(cid:20)
&
3
O
(
(cid:31)
h
0
5
(cid:2)
(cid:11)
(cid:19)
M
%
N
x
(cid:15)
e
9
(cid:17)
Y
(cid:0)
>
(cid:11)
(cid:20)
O
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
[
N
O
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:11)
(cid:19)
M
N
x
(cid:15)
e
(cid:17)
P
(cid:0)
(cid:4)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:31)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
[
@
N
(cid:21)
(cid:31)
(cid:15)
W
X
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
‘
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
(cid:28)
(cid:29)
(cid:5)
(cid:30)
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:5)
$
%
&
(cid:6)
N
(
)
*
+
,
(cid:7)
#
(cid:29)
(cid:19)
.
3
(cid:14)
8
)

(cid:16)
(cid:24)
(cid:2)
}
7
&
t
K
+
:
(cid:0)
(cid:2)
(cid:7)
$
.
&
N
t
(cid:31)
*
0
P
(cid:0)
(cid:7)
(cid:11)
(cid:26)
$
&
(cid:129)
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
(cid:11)
M
&
N
O
(
(cid:15)
*
0
5
P
>
(cid:29)
(cid:26)
(cid:20)
&
3
(cid:13)
O
(
K

0
(cid:3)
$
T
’
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
r
$
@
(cid:6)
N
(cid:31)
(cid:15)
*
5
P
(cid:7)
M
N
O
)
*
P
(cid:0)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:19)
@
3
(cid:14)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
%
‘
(
+
:
(cid:0)
(cid:2)
(cid:7)
‘
3
(

0
(cid:2)
(cid:7)
(cid:3)
(cid:29)
(cid:5)
(cid:19)
%
H
(cid:14)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
$
l
N
(
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
M
@
N
x
e
(cid:24)
P
(cid:0)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
.
(cid:13)
8
(cid:0)
(cid:7)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
r
H
K
h
5
(cid:2)
(cid:7)
(cid:8)
T
N
O
8
*
9
,
(cid:0)
(cid:9)
(cid:7)
(cid:28)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
l
(cid:129)
(
(cid:15)
*
0
5
P
(cid:0)
(cid:29)
(cid:20)
@
3
O
)

(cid:2)
(cid:8)
(cid:3)
T
3
8

9
:
(cid:2)
(cid:7)
(cid:29)
(cid:19)
%
3
(cid:14)
)

(cid:16)
9
(cid:24)
:
(cid:2)
(cid:8)
2
7
3
8

9
:
(cid:2)
(cid:7)
(cid:5)
(cid:19)
%
(cid:6)
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:2)
>
p
&
(cid:6)
(
(cid:31)
(cid:15)
0
5
(cid:2)
(cid:7)
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
(cid:28)
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
‘
(cid:129)
(cid:14)
(
e
+
(cid:24)
,
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:12)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
}
(cid:5)
(cid:6)
K
(cid:2)
(cid:7)
(cid:8)
(cid:3)
p
$
.
&
(cid:6)
N
t
(cid:31)
(cid:15)
*
0
5
P
@
N
O
*
P
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
(cid:30)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:26)
%
@
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
7
(cid:6)
8
(cid:15)
9
5
:
(cid:2)
r
(cid:20)
H
O
h
5
(cid:2)
(cid:8)
(cid:5)
(cid:20)
%
(cid:6)
O
)
9
:
(cid:2)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:23)
(cid:13)
(cid:14)
(cid:31)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
$
‘
(cid:6)
N
(
(cid:31)
*
0
P
(cid:7)
$
@
’
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
2
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:11)
(cid:19)
$
%
N
(cid:14)
(cid:15)
e
9
(cid:17)
,
(cid:0)
(cid:11)
(cid:20)
&
O
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
>
(cid:11)
[
&
N
O
(
(cid:31)
(cid:15)
*
0
5
P
(cid:4)
(cid:11)
[
N
O
(cid:31)
(cid:15)
*
5
P
(cid:0)
(cid:11)
(cid:19)
M
3
N
x
h
e
(cid:17)
P
(cid:4)
(cid:19)
(cid:20)
%
x
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:29)
(cid:11)
(cid:19)
.
@
3
(cid:14)
8
(cid:31)
h
(cid:16)
(cid:17)
(cid:2)
%
@
N
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
p
(cid:19)
(cid:6)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:16)
(cid:24)
(cid:8)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:15)
5
(cid:7)
(cid:8)
(cid:20)
(cid:6)
O
(cid:2)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:15)
5
(cid:7)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:12)
(cid:20)
(cid:13)
x
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:26)
(cid:20)
(cid:13)
O
(cid:15)
5
(cid:0)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
(cid:12)
$
’
(cid:14)
V
W
(cid:24)
P
(cid:0)
(cid:28)
(cid:19)
$
.
N
(cid:14)
8
V
e
(cid:24)
P
}
$
.
&
N
/
K
*
0
P
(cid:0)
(cid:7)
(cid:4)
$
.
&
N
t
)
*
0
P
(cid:0)
(cid:7)
(cid:29)
(cid:5)
(cid:19)
.
(cid:30)
(cid:14)
8
)

(cid:16)
(cid:24)
(cid:2)
>
(cid:29)
(cid:5)
7
(cid:30)
8
K

9
:
(cid:2)
(cid:7)
(cid:29)
$
T
3
N
8
(cid:31)

*
9
,
(cid:7)
(cid:5)
(cid:26)
$
%
&
(cid:6)
’
(
(cid:31)
*
+
,
(cid:7)
(cid:29)
(cid:11)
(cid:26)
$
3
(cid:129)
(cid:31)
h
*
5
P
(cid:7)
[
%
&
N
O
(
(cid:31)
*
+
,
(cid:0)
(cid:26)
$
&
’
(
*
0
P
(cid:0)
(cid:7)
(cid:28)
(cid:29)
(cid:26)
&
3
(cid:13)
(
V

0
(cid:7)
(cid:3)
(cid:11)
$
T
&
N
/
(cid:15)
*
\
5
,
(cid:0)
(cid:29)
(cid:11)
(cid:20)
&
3
O
(
4
0
5
(cid:2)
#
(cid:29)
(cid:20)
%
&
3
O
(
)

+
:
(cid:2)
(cid:11)
(cid:26)
T
&
3
(cid:13)
/
4
\
5
:
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
2
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
$
%
@
(cid:6)
N
(cid:14)
)
e
9
(cid:24)
,
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:26)
(cid:13)
V
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
$
.
N
8
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:29)
$
@
3
N

*
P
(cid:7)
(cid:8)
(cid:29)
%
@
3
(cid:31)

9
:
(cid:2)
(cid:7)
(cid:8)
$
%
‘
N
(
*
+
,
(cid:0)
(cid:7)
(cid:5)
@
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
%
@
3

9
:
(cid:2)
(cid:7)
(cid:8)
#
(cid:19)
%
(cid:14)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:26)
&
(cid:13)
(
0
(cid:0)
(cid:7)
(cid:3)
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
p
%
&
(cid:30)
(
4
+
5
:
(cid:2)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
$
@
(cid:6)
N
V
*
P
(cid:7)
(cid:8)
$
.
N
8
*
P
(cid:0)
(cid:7)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
U
(cid:5)
(cid:19)
(cid:30)
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
$
%
(cid:6)
N
(cid:14)
W
9
(cid:24)
Y
(cid:19)
@
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:11)
(cid:26)
(cid:13)
(cid:31)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:11)
[
N
O
(cid:15)
*
5
P
(cid:0)
(cid:26)
(cid:20)
(cid:13)
O
)
(cid:0)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
.
3
(cid:13)
8
h
5
(cid:7)
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
r
&
H
(
(cid:31)
h
0
5
(cid:2)
(cid:7)
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
(cid:9)
(cid:7)
>
(cid:4)
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
$
@
’
(cid:14)
(cid:31)
(cid:15)
W
(cid:17)
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
>
(cid:4)
(cid:26)
(cid:13)
K
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:19)
$
.
N
(cid:14)
8
V
W
(cid:24)
P
>
$
.
@
N
8
K
*
P
(cid:0)
(cid:7)
>
(cid:4)
$
.
N
8
K
*
P
(cid:0)
(cid:7)
(cid:5)
(cid:19)
$
.
(cid:30)
N
(cid:14)
8

W
(cid:24)
(cid:26)
%
(cid:6)
(cid:13)
9
:
(cid:7)
(cid:8)
(cid:29)
(cid:26)
3
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
&
’
(
*
+
,
(cid:0)
(cid:7)
(cid:11)
(cid:26)
l
3
(cid:13)
(
h
0
5
(cid:7)
(cid:29)
(cid:20)
%
3
O

9
:
(cid:2)
(cid:8)
2
(cid:11)
%
&
3
(
4
\
5
:
(cid:2)
(cid:23)
(cid:20)
%
(cid:13)
(cid:21)
(cid:15)
(cid:16)
9
X
:
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
>
(cid:29)
(cid:26)
&
3
(cid:13)
(
(cid:31)

0
(cid:7)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
$
%
l
N
(
)
*
\
Y
(cid:0)
(cid:7)
(cid:19)
.
@
3
(cid:14)
8

(cid:16)
(cid:24)
(cid:2)
(cid:5)
%
(cid:6)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:5)
(cid:19)
@
(cid:6)
(cid:14)
)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
@
3
V

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:5)
$
7
(cid:30)
N
8
(cid:31)

*
9
Y
(cid:7)
(cid:29)
(cid:26)
$
%
3
’

*
9
,
(cid:7)
(cid:8)
(cid:29)
%
@
3

9
:
(cid:2)
(cid:7)
(cid:8)
(cid:26)
%
&
(cid:13)
(
\
:
(cid:0)
(cid:7)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:11)
&
3
(
h
0
5
(cid:2)
(cid:7)
(cid:26)
(cid:20)
%
&
(cid:13)
O
(
)
\
:
(cid:0)
(cid:11)
.
3
8
4
5
(cid:2)
(cid:7)
(cid:29)
(cid:19)
(cid:20)
%
3
(cid:21)

(cid:16)
9
(cid:24)
:
(cid:2)
%
@
(cid:13)
9
:
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
$
@
N
(cid:15)
*
5
P
(cid:0)
(cid:7)
(cid:19)
(cid:20)
(cid:21)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
p
.
(cid:6)
8
(cid:31)
(cid:15)
5
(cid:2)
(cid:7)
>
(cid:4)
[
N
O
K
*
P
(cid:0)
(cid:8)
(cid:19)
$
.
N
(cid:14)
8
W
(cid:24)
P
(cid:4)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:31)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:5)
(cid:19)
$
(cid:6)
N
(cid:14)
W
(cid:24)
P
>
(cid:29)
@
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
N
*
9
,
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
4
5
(cid:7)
(cid:8)
(cid:26)
(cid:20)
%
(cid:13)
O
(cid:15)
9
5
:
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:26)
&
3
(cid:13)
(
h
0
5
(cid:7)
(cid:20)
%
O
9
:
(cid:0)
(cid:2)
(cid:8)
(cid:4)
(cid:11)
&
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
(cid:21)
)
h
(cid:16)
(cid:17)
(cid:2)
(cid:8)
7
O
8
9
:
(cid:0)
(cid:2)
(cid:9)
(cid:7)
}
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:19)
$
‘
(cid:6)
N
(cid:14)
(
(cid:15)
e
0
(cid:17)
#
(cid:20)
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:4)
.
&
t
(cid:31)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:19)
$
@
N
(cid:14)
(cid:15)
e
(cid:17)
P
(cid:0)
(cid:19)
(cid:20)
@
(cid:21)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
>
(cid:4)
.
8
V
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:19)
$
.
@
N
(cid:14)
8
K
e
(cid:24)
P
$
.
N
8
*
P
(cid:0)
(cid:7)
(cid:29)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:11)
%
&
3
(
h
+
5
:
(cid:2)
(cid:20)
%
&
O
(
\
:
(cid:0)
(cid:2)
2
(cid:11)
(cid:19)
3
(cid:14)
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:19)
(cid:20)
%
&
(cid:21)
(
(cid:16)
\
(cid:24)
:
(cid:0)
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:19)
&
(cid:14)
(
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
p
(cid:19)
&
(cid:6)
(cid:14)
(
)
(cid:15)
(cid:16)
0
(cid:17)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
(cid:9)
(cid:7)
#
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
(cid:11)
l
(
K
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:19)
M
.
N
x
8
(cid:15)
e
(cid:17)
P
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:4)
l
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
.
(cid:14)
8
)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:19)
(cid:20)
.
(cid:21)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:20)
@
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
&
(cid:21)
(
)
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:2)
(cid:20)
.
O
8
)
(cid:0)
(cid:2)
(cid:3)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
p
(cid:19)
(cid:6)
(cid:14)
)
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:8)
>
(cid:11)
(cid:20)
.
&
O
/
K
(cid:15)
0
5
(cid:0)
(cid:2)
.
N
O
8
*
P
(cid:0)
(cid:9)
(cid:7)
}
(cid:4)
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
(cid:11)
(cid:19)
$
&
N
(cid:14)
(
(cid:15)
e
0
(cid:17)
P
(cid:19)
(cid:20)
l
(cid:21)
(
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:4)
(cid:19)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
#
(cid:11)
(cid:23)
&
(cid:13)
(cid:14)
(
)
(cid:15)
(cid:16)
0
X
(cid:0)
(cid:20)
.
&
O
/
)
0
(cid:0)
(cid:2)
(cid:3)
(cid:26)
.
(cid:13)
8
(cid:15)
5
(cid:0)
(cid:7)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
#
(cid:4)
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:4)
(cid:19)
.
&
(cid:14)
/
)
(cid:16)
0
(cid:24)
(cid:0)
(cid:2)
(cid:19)
.
(cid:6)
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:2)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
}
(cid:4)
&
(
K
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:19)
$
.
&
(cid:6)
N
(cid:14)
t
(cid:15)
e
0
(cid:17)
@
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
#
(cid:4)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:12)
l
(cid:13)
(cid:14)
(
)
(cid:15)
(cid:16)
0
(cid:17)
(cid:0)
(cid:11)
(cid:20)
.
O
8
)
(cid:15)
5
(cid:0)
(cid:2)
.
O
8
(cid:0)
(cid:2)
(cid:3)
#
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
)
4
5
(cid:7)
(cid:8)
(cid:20)
T
&
O
/
)
\
:
(cid:0)
(cid:2)
(cid:29)
(cid:11)
.
3
8
4
5
(cid:2)
(cid:7)
(cid:11)
(cid:26)
(cid:20)
%
&
3
(cid:13)
O
(
h
+
5
(cid:20)
%
(cid:6)
O
9
:
(cid:2)
(cid:8)
(cid:4)
(cid:26)
(cid:13)
(cid:31)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
(cid:5)
(cid:19)
$
(cid:6)
N
(cid:14)
K
e
(cid:24)
P
(cid:19)
$
.
N
(cid:14)
8
W
(cid:24)
P
#
(cid:5)
(cid:19)
(cid:6)
(cid:14)
)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
>
(cid:5)
.
&
(cid:6)
/
K
0
(cid:2)
(cid:7)
(cid:3)
(cid:11)
$
.
N
8
(cid:15)
*
5
P
(cid:0)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
>
r
l
(cid:6)
(
K
(cid:15)
0
5
(cid:2)
(cid:7)
.
N
O
8
*
P
(cid:0)
(cid:9)
(cid:7)
#
U
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:23)
%
&
(cid:13)
(cid:14)
(
)
(cid:16)
+
(cid:24)
:
(cid:26)
.
&
(cid:13)
/
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:29)
(cid:20)
3
O

(cid:2)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
%
&
(cid:13)
(
(cid:15)
+
5
:
(cid:0)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
#
(cid:29)
&
3
(

0
(cid:2)
(cid:7)
(cid:3)
(cid:26)
%
&
(cid:13)
(
\
:
(cid:0)
(cid:7)
(cid:29)
(cid:5)
(cid:26)
(cid:30)
(cid:13)
(cid:31)

(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
(cid:6)
’
*
9
,
(cid:7)
(cid:8)
>
(cid:26)
@
(cid:13)
V
(cid:0)
(cid:7)
(cid:8)
(cid:3)
$
.
@
N
8
)
*
P
(cid:0)
(cid:7)
>
(cid:4)
.
8
V
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:19)
$
.
N
(cid:14)
8
(cid:31)
e
(cid:24)
P
$
l
N
(
*
0
P
(cid:0)
(cid:7)
#
(cid:23)
(cid:13)
(cid:14)
)
(cid:16)
(cid:24)
(cid:0)
(cid:8)
(cid:5)
.
&
(cid:6)
/
(cid:31)
0
(cid:2)
(cid:7)
(cid:3)
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
(cid:29)
(cid:5)
H

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:29)
(cid:26)
%
3
(cid:13)
)

9
:
(cid:7)
(cid:8)
T
&
/
\
:
(cid:0)
(cid:2)
(cid:7)
#
(cid:29)
(cid:11)
(cid:19)
3
(cid:14)
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:26)
(cid:20)
%
&
(cid:13)
O
(
(cid:15)
+
5
:
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:26)
3
(cid:13)
4
5
(cid:7)
(cid:8)
(cid:5)
(cid:20)
%
(cid:30)
O

9
:
(cid:2)
(cid:8)
>
(cid:29)
(cid:26)
%
3
(cid:13)
(cid:31)

9
:
(cid:7)
(cid:8)
U
$
%
@
3
N
(cid:31)

*
9
,
(cid:7)
(cid:8)
(cid:12)
$
%
(cid:6)
’
(cid:14)
W
9
(cid:24)
Y
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
@
(cid:6)
(cid:14)
)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
.
@
3
8

(cid:2)
(cid:7)
(cid:3)
(cid:4)
(cid:5)
%
(cid:6)
)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:29)
p
(cid:19)
.
(cid:30)
(cid:14)
8
(cid:31)
4
(cid:16)
(cid:17)
(cid:2)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
$
%
(cid:129)
(cid:15)
*
9
5
Y
(cid:0)
(cid:7)
(cid:20)
O
(cid:0)
(cid:2)
(cid:8)
(cid:3)
#
(cid:29)
&
3
(
)

0
(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:26)
T
&
3
(cid:13)
/
4
\
5
:
(cid:29)
(cid:20)
%
3
O

9
:
(cid:2)
(cid:8)
p
%
&
(cid:6)
(
(cid:15)
+
5
:
(cid:2)
>
(cid:29)
(cid:11)
(cid:20)
3
O
(cid:31)
h
5
(cid:2)
(cid:8)
[
%
N
O
*
9
,
(cid:0)
(cid:8)
(cid:29)
@
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:4)
%
@
V
9
:
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:4)
(cid:19)
$
.
N
(cid:14)
8
(cid:31)
e
(cid:24)
P
(cid:4)
(cid:5)
(cid:19)
$
(cid:6)
N
(cid:14)
(cid:31)
e
(cid:24)
P
>
(cid:4)
(cid:12)
$
’
(cid:14)
V
W
(cid:24)
P
(cid:0)
(cid:19)
$
.
N
(cid:14)
8
e
(cid:24)
P
(cid:5)
(cid:6)
(cid:31)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:5)
$
&
(cid:6)
N
(
V
*
0
P
(cid:7)
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
(cid:28)
(cid:29)
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
$
%
‘
’
(
(cid:15)
*
+
5
,
(cid:0)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:4)
%
&
(
+
:
(cid:0)
(cid:2)
(cid:7)
#
(cid:19)
(cid:14)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:26)
&
(cid:13)
(
(cid:31)
0
(cid:0)
(cid:7)
(cid:3)
(cid:26)
$
&
(cid:129)
(
*
0
P
(cid:0)
(cid:7)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
(cid:26)
(cid:6)
(cid:13)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
@
(cid:6)
)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
.
@
3
8
V

(cid:2)
(cid:7)
(cid:3)
$
7
@
N
8
)
*
9
Y
(cid:0)
(cid:7)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:4)
.
8
(cid:31)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
(cid:19)
$
@
(cid:6)
N
(cid:14)
(cid:31)
W
(cid:24)
P
$
@
(cid:129)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:26)
%
l
3
(cid:13)
(
h
\
5
:
(cid:20)
%
(cid:13)
O
9
:
(cid:0)
(cid:8)
(cid:11)
(cid:26)
(cid:13)
(cid:15)
5
(cid:0)
(cid:7)
(cid:8)
(cid:20)
(cid:6)
O
(cid:15)
5
(cid:2)
(cid:8)
(cid:29)
(cid:26)
(cid:20)
3
(cid:13)
O
)

(cid:8)
(cid:3)
(cid:5)
7
(cid:30)
8

9
:
(cid:2)
(cid:7)
%
@
(cid:6)
9
:
(cid:2)
(cid:7)
(cid:8)
(cid:29)
r
(cid:26)
H
(cid:13)
(cid:31)
h
5
(cid:7)
(cid:8)
(cid:5)
[
%
(cid:30)
N
O

*
9
,
(cid:8)
(cid:5)
(cid:26)
%
(cid:6)
(cid:13)
(cid:31)
9
:
(cid:7)
(cid:8)
(cid:4)
(cid:26)
$
’
(cid:31)
*
P
(cid:0)
(cid:7)
(cid:8)
(cid:12)
$
’
(cid:14)
W
(cid:24)
P
(cid:0)
@
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:5)
(cid:19)
(cid:6)
(cid:14)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
>
(cid:29)
(cid:5)
(cid:19)
@
(cid:30)
(cid:14)
K

(cid:16)
(cid:24)
(cid:2)
(cid:8)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:29)
3

(cid:2)
(cid:7)
(cid:8)
(cid:3)
2
(cid:11)
%
&
3
(
4
\
5
:
(cid:2)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
%
3
(cid:21)
h
(cid:16)
9
(cid:17)
:
(cid:2)
(cid:11)
(cid:20)
%
&
O
(
(cid:15)
\
5
:
(cid:0)
2
(cid:11)
(cid:20)
&
3
O
(
(cid:31)
4
0
5
(cid:2)
(cid:11)
(cid:19)
[
%
N
(cid:21)
(cid:15)
W
9
X
,
(cid:0)
>
(cid:11)
(cid:20)
O
(cid:31)
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:29)
(cid:11)
M
3
N
O
(cid:31)
h
*
5
P
>
[
%
&
N
O
(
(cid:31)
*
+
,
(cid:0)
>
(cid:29)
(cid:11)
$
@
3
N
(cid:31)
h
*
5
P
(cid:7)
2
[
%
3
N
O
(cid:31)

*
9
,
(cid:8)
(cid:19)
$
%
@
3
N
(cid:14)

e
9
(cid:24)
,
(cid:4)
(cid:19)
%
@
(cid:14)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
(cid:4)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:31)
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:4)
(cid:11)
(cid:19)
M
N
x
(cid:31)
(cid:15)
e
(cid:17)
P
(cid:0)
>
(cid:4)
(cid:19)
[
N
(cid:21)
K
W
(cid:24)
P
(cid:0)
>
(cid:19)
$
.
N
(cid:14)
8
V
W
(cid:24)
P
.
@
N
8
*
P
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
&
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
l
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
@
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:4)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
(cid:9)
(cid:7)
}
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:11)
(cid:20)
O
(cid:15)
5
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
(cid:6)
x
(cid:15)
(cid:16)
X
(cid:2)
(cid:8)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:28)
.
&
t
V
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
$
.
&
N
/
(cid:15)
*
0
5
P
(cid:0)
#
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
>
(cid:29)
(cid:5)
.
&
H
t
V

0
(cid:2)
(cid:7)
(cid:3)
$
7
(cid:129)
8
*
9
Y
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:23)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:0)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:19)
(cid:20)
x
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
l
(cid:6)
(
(cid:15)
0
5
(cid:2)
(cid:7)
(cid:20)
(cid:13)
O
(cid:0)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
(cid:26)
$
%
&
(cid:129)
(
)
*
\
Y
(cid:0)
(cid:7)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:5)
.
&
(cid:6)
t
)
0
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:29)
r
.
&
H
/
(cid:31)
h
0
5
(cid:2)
(cid:7)
[
%
(cid:129)
O
*
9
,
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:5)
(cid:6)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:23)
(cid:6)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
X
(cid:8)
r
(cid:20)
(cid:6)
O
(cid:31)
(cid:15)
5
(cid:2)
(cid:8)
M
N
O
*
P
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
&
H
(
(cid:31)

0
(cid:2)
(cid:7)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:28)
(cid:26)
$
%
&
(cid:129)
(
V
*
\
Y
(cid:0)
(cid:7)
(cid:11)
(cid:26)
$
.
&
(cid:129)
/
(cid:31)
(cid:15)
*
0
5
P
(cid:0)
@
N
O
*
P
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:29)
(cid:11)
(cid:19)
$
%
@
3
N
(cid:14)
4
W
9
X
Y
%
‘
O
(
+
:
(cid:0)
(cid:2)
@
(cid:13)
(cid:0)
(cid:7)
(cid:8)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
.
3
8
h
5
(cid:2)
(cid:7)
(cid:19)
(cid:20)
%
x
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
>
(cid:29)
(cid:23)
3
(cid:13)
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
2
(cid:20)
3
O
)

(cid:2)
(cid:8)
(cid:3)
(cid:29)
(cid:19)
7
3
(cid:14)
8
)

(cid:16)
9
(cid:24)
:
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
(cid:12)
(cid:13)
(cid:14)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:8)
(cid:20)
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
(cid:11)
.
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:19)
(cid:20)
3
x
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:4)
(cid:20)
%
&
O
(
)
+
:
(cid:0)
(cid:2)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:29)
(cid:19)
(cid:20)
3
x
)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
@
8
9
:
(cid:0)
(cid:2)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
.
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
#
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
(cid:11)
.
&
/
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
.
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
(cid:19)
H
(cid:14)
(cid:31)

(cid:16)
(cid:24)
(cid:2)
(cid:8)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:4)
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
>
(cid:29)
(cid:19)
(cid:20)
3
(cid:21)
K

(cid:16)
(cid:24)
(cid:2)
(cid:8)
T
@
N
8
*
9
,
(cid:0)
(cid:7)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
.
&
t
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
#
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
(cid:11)
.
&
/
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
#
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:4)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:19)
.
(cid:14)
8
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:4)
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:4)
(cid:19)
(cid:20)
(cid:21)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
.
&
t
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
#
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
(cid:11)
.
&
/
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
#
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:4)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:19)
.
(cid:14)
8
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
(cid:21)
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:4)
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
(cid:17)
(cid:0)
(cid:2)
(cid:4)
(cid:19)
(cid:20)
(cid:21)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:11)
.
&
t
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
#
(cid:20)
&
O
(
)
0
(cid:0)
(cid:2)
(cid:3)
(cid:11)
.
&
/
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
#
(cid:19)
(cid:20)
x
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:4)
.
&
/
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:19)
.
(cid:14)
8
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:20)
&
O
(
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:19)
(cid:20)
(cid:21)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:26)
&
(cid:13)
(
(cid:15)
0
5
(cid:0)
(cid:7)
(cid:5)
(cid:19)
(cid:20)
(cid:6)
x
)
(cid:16)
(cid:24)
(cid:2)
(cid:8)
(cid:11)
.
8
(cid:15)
5
(cid:0)
(cid:2)
(cid:7)
(cid:4)
(cid:19)
(cid:20)
(cid:21)
)
(cid:16)
(cid:24)
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
.
(cid:14)
8
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
(cid:29)
(cid:12)
3
(cid:13)
(cid:14)
)

(cid:16)
(cid:24)
(cid:8)
7
&
(cid:6)
t
+
:
(cid:2)
(cid:7)
}
(cid:26)
(cid:13)
K
(cid:0)
(cid:7)
(cid:8)
(cid:3)
$
.
&
(cid:6)
N
t
(cid:15)
*
0
5
P
#
(cid:20)
O
)
(cid:0)
(cid:2)
(cid:8)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
>
(cid:29)
(cid:5)
H
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
$
%
@
(cid:129)
*
9
Y
(cid:0)
(cid:7)
(cid:8)
(cid:9)
(cid:7)
=
>
U
3
(cid:31)

(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:11)
(cid:19)
$
%
@
N
(cid:14)
(cid:15)
W
9
X
Y
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
3
x
4
(cid:16)
X
(cid:2)
(cid:8)
(cid:19)
(cid:20)
%
(cid:21)
)
(cid:16)
9
(cid:24)
:
(cid:0)
(cid:2)
U
(cid:11)
.
3
8
(cid:31)
h
5
(cid:2)
(cid:7)
(cid:19)
M
%
N
x
e
9
(cid:24)
Y
(cid:0)
(cid:4)
(cid:11)
‘
(
(cid:31)
(cid:15)
0
5
(cid:0)
(cid:2)
(cid:7)
(cid:11)
(cid:19)
[
N
(cid:21)
(cid:15)
W
X
P
(cid:0)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
(cid:11)
(cid:19)
(cid:20)
x
(cid:15)
(cid:16)
X
(cid:0)
(cid:2)
(cid:8)
>
(cid:29)
(cid:11)
(cid:19)
(cid:20)
3
x
(cid:31)
4
(cid:16)
X
(cid:2)
(cid:8)
%
@
N
O
*
9
Y
(cid:0)
(cid:8)
(cid:9)
(cid:7)
=
#
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
8
)
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
@
)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
.
&
t
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
‘
(
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
#
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
.
&
t
)
0
(cid:0)
(cid:2)
(cid:7)
(cid:3)
@
8
(cid:0)
(cid:2)
(cid:7)
(cid:3)
(cid:9)
(cid:7)
100

ANSWERS TO EXERCISES

7.2.2.4

1

−

−

−

2k

(k, n
j). The proof is by induction on k: Vertex v(0, j) is in the top row
and has out-degree 1, so its move can only go west (left). When k > 0, the move from
v(k, j) can’t go northeast or north to a vertex whose predecessor is already known. Nor
can it go northwest, except perhaps when j has its maximum value; but that move is
also impossible, because the northwest vertex must belong to a coil for smaller k.

Similarly, the arcs from (k, 2k + 1 + j) must go west. And symmetrically, the arcs

pi, as random source
introverted edge
introverted
extroverted

from (m

1

k, n
−
Now we obtain an m

2k

−

−

−

2

−
(n

j) and (m

1

k, 2k + 1 + j) must go east.

−

−

2) tour by removing two arcs in each row, namely the
two forced arcs that are nearest the center. We also shift all of the “extreme” vertices
in a row (those that don’t lie between the two removed arcs), one column towards the
14:
center, with their arcs., For example, here’s how a “random” 8

16 tour becomes 8

−

×

×

×

=

⇒

236. The nonzero values are X3,3 = 1; X4,4 = 8 = 4
X4,6 = X4,8 = 50 = 2
8 + 4
144 = 2
12+4
X6,8 = 308637 = 1
·
X7,8 = 9210632 = 2
Here are some of the attractive examples with diﬀerent kinds of 4-way symmetry:

·
777, X6,7 = 545278 = 2
4 + 4
12708 + 8

9 + 4
30; X6,6 = 6480 = 2
·
898 + 4

76704; X7,7 = 552960 = 2
2301585; X8,8 = 237059136 = 4

2, X4,5 = 72 = 2
·
46; X5,5 = 128 = 8

8, X4,7 = 200 = 2
63+8
6+4

4 + 4
16,
16, X5,6 =
136014,
69072,
29626038.

·
·
611+4
·
94 + 8

25 + 2
2146 + 4

·
·

·
·

·

·

·

·

·

·

·

·

·

·

·

·

·

·

240. True. The edges of (53) are clearly distinct when the vertices are distinct, unless
perhaps l = 2 and t0 = t2. But even then, t0 []0[]1 t1 is never the same as t1 []1[]2 t0.
241. Let the edges be u []0[]1 x []1[]2 y []2[]3 x []3[]4 v, with arbitrary arrows []0, . . . , []4.
242. (a) (i) 2

n!; (ii) 2

−

−

n

n

1

1

(b) (i) n!; (ii) (n
(c) (i) (n+1)!/2 (at most one introverted edge); (ii) (n

1)!

−

·

(n
1)!.
−
[n even].

1)! (no introverted edges).

−

244. Create bidirected graphs without directed edges, as in (54). Then problem (a)
has 20293176 solutions (found in 8.7 Gμ); (b) has 127119280 (found in 52.1 Gμ).

245. Half true: A directed graph B (having no introverted or extroverted edges) always
leads to a bipartite G(B), with the natural partition into positive and negative vertices.
But G(B) can also be bipartite in many other cases — such as when B is obtained

as in (54) from graphs G and H that are themselves bipartite.

December 4, 2025

(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:3)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:0)
(cid:2)
(cid:7)
(cid:8)
(cid:3)
(cid:9)
(cid:8)
(cid:9)
(cid:7)
bidirected graph
purge
topological sorting

7.2.2.4

ANSWERS TO EXERCISES

101

246. Let B have three vertices
edges are v (cid:5)(cid:5) vL, v (cid:5)(cid:5) vR, v (cid:4)(cid:4) vL, v (cid:4)(cid:4) vR for all v; also uL (cid:5)(cid:4) vR when u
in G, uL (cid:4)(cid:5) vR when u

for each vertex v of G and H. Its bidirected
v
v in H. The Hamiltonian cycles of B fall into a pattern

v, vL, vR

→

{

}

⇒
uR (cid:5)(cid:5) u (cid:5)(cid:5) uL (cid:5)(cid:4) vR (cid:4)(cid:4) v (cid:4)(cid:4) vL (cid:4)(cid:5) wR (cid:5)(cid:5) w (cid:5)(cid:5) wL

when u

v

w.

·

→

· · ·

4 + 4

· · ·
247. The construction of answer 246 yields a bidirected graph with 192 vertices, 536
edges, and 44 = 8
3 Hamiltonian
cycles (found in just 252 kilomems!). One of
the three essentially diﬀerent symmetrical
solutions is shown, together with one of the
4
9. (There are 14544
·
10 solutions, found in 139 Mμ; 8151216
10
12 solutions, found in 41 Gμ.)
12

1 64 23 22 47 46 61 60
24 9 8 63 62 21 20 45
25 2 49 48 7 6 59 44
50 3 10 37 36 43 58 19
51 26 11 4 5 42 35 18
12 27 38 39 16 17 34 57
13 52 53 30 31 40 41 56
28 29 14 15 54 55 32 33

1 72 55 54 15 14 69 68 35
56 17 16 71 70 37 36 51 34
57 2 25 24 53 52 13 50 67
18 3 58 39 38 23 12 33 66
19 40 59 26 27 22 65 32 49
4 41 20 21 8 9 64 11 48
5 60 61 44 45 28 29 10 31
42 43 6 7 62 63 46 47 30

3 solutions of size 8

⇒

×

·

×
×

ARCS(v), do the following while a
1) & 1), w(cid:2)
2w + (((
2v + ((l

250. Start with ADJ[v][w]
a
v(cid:2)
insert(v(cid:2), w(cid:2)) and insert(w(cid:2), v(cid:2)); set a
w, ADJ[v][w]
DEG(v), NBR[v][d]

←
←

← ∞

(cid:31)

←

≤

v, w < 2n. Then for 0
TIP(a) and l
= Λ: Set w
= w and ADJ[v(cid:2)][w(cid:2)] =
l)
NEXT(a). Here ‘insert(v, w)’ means ‘set d
d, DEG(v)

v < n and
LEN(a); set
,

1) & 1); if v

∞
←

d + 1’.

≤
←

(cid:31)

←

for 0

←

←

−
←
←

251. First do step B4. Then purge(CURU, CURV) and purge(CURV, CURU) (see answer 112).
Then makeinner(CURU) and makeinner(CURV); activate(CURU
1);
makemates(CURU
1).

1) and activate(CURV

1, CURV

⊕

⊕

⊕
252. (a) makeinner(u); activate(u

⊕

⊕
(b) deactivate(u); makemates(v

1); makemates(u
1, MATE(u)).

1, v

1).

⊕

⊕

⊕

(cid:31)

←

← −

EU[k]

1 and j

253. We use ﬁve arrays (x, xs, y, ys, sg) of length n and two arrays (v, vs) of
length n + 1. Start with xk
k < n do this: Set
EU[k] & 1,
i
i,
xsi
sgj

j, sgi
EV[k] & 1. If xj < 0, set xj

1 for 0
1.
j and ysi

←
EU[k] & 1; otherwise set yj

EV[k]
EV[k] & 1; otherwise set yi
EV[k] & 1, xsj
Then set v0

ys0; otherwise
1 = sgj? yj: xj),
1 = sgj? ysj: xsj). This yields (53) with l = n, u = v = 0, tk = vk, and

xs0. For k = 2, . . . , n, set j

←
y0 and vs1
(vsk
1, vk

←
1. If sg0 = 1, set v1

If xi < 0, set xi

←
0 and vs0

k < n. For 0

EU[k] & 1.

x0 and vs1

i and ysj

(cid:31)
←

←
←

←
−

←
−

←

←

←

←

←

←

←

←

←

vk

≤

≤

set v1
←
vsk
(vsk
[]k = (vsk = 1? (cid:5): (cid:4)).

←

−

254. Steps B15 and B16 backtrack to level 0, and remove the ﬁrst root edge ‘0−
1−’
from the graph. Now 0− and 1− have degree 1; so they go onto the trigger stack. The
2− is quickly forced; and the second Hamilto-
1−
0−
subpath 0
+
+
nian matching is visited, namely
. There are no others.

2
0−

−−−
1

, 1−

, 2−

−−−

−−−

−−−

−−−

1

2

0

+

+

+

+

−−−

−−−

−−−

}

−−−
{

256. In answer 250 (for step B1), let v(cid:2) = 2v and w(cid:2) = 2w + 1.
In place of answer 253 (for step B13), ﬁrst do this for 0

i, otherwise set xi

k < n: Set i

1
0
←
xk. The desired Hamiltonian cycle is

←
j. Then set k

(cid:31)
←

EU[k]

≤

←

EV[k]

and j
and, for j = 0, 1, . . . , n, do this: vj
0 = v0

vn = 0.

1; if EU[k] & 1 = 1, set xj

(cid:31)

←

v1

k, k

←

←

−−→

−−→ · · · −−→

270. (a) v1

vn in G if and only if s

v1

vn

t

s in

G.

−−→ · · · −−→
(b) Suppose u1

un and v1

−−→ · · · −−→

= vj
and j minimum. Then uj = vk and vj = ul for some k > j and l > j. Consequently
ul

vj+1
(c) True. We can assume that the vertices of G are labeled “topologically” (see
v1,

vk implies j < k. Algorithm B will choose t

Algorithm 2.2.3T) so that vj

ul is a cycle.

−−→· · · −−→

−−→ · · · −−→

uj+1

−−→

−−→

vk

(cid:7)

s

−−→· · · −−→

−−→
vn are Hamiltonian, with uj

−−→

−−→
−−→ · · · −−→

−−→

−−→

−−→

December 4, 2025

(cid:12)
(cid:12)
(cid:12)
102

ANSWERS TO EXERCISES

7.2.2.4

1

−

v1, . . . , vk

since s and v1 have in-degree 1. If v1

1, then
are inner; hence vk+1 has in-degree 0 or 1. No backtracking is needed.

vk have been chosen, for k

−−→ · · · −−→

{
271. Construct O(n
G by removing one arc from each cycle in all possi-
ble ways. Then G has a Hamiltonian path if and only if at least one of those subgraphs
is Hamiltonian. And each subgraph can be tested in O(m + n) steps by exercise 270(c).

) subgraphs of

≥

(cid:7)

}

p

(Of course this result is purely theoretical, by no means practical!)

theoretical
practical
strictly alternating
knight-and-wazir
disjoint oriented cycles

(cid:7)

· · ·

· · ·

· · ·

[] z

z []

a []

(cid:4) t (cid:4)(cid:4) s and s (cid:4)

z of G corresponds to exactly two Hamiltonian cycles of

272. Deﬁne
G by generalizing exercise 270: The bidirected edges involving the new
vertices s and t are now s (cid:4)(cid:4) v, s (cid:4)(cid:5) v, v (cid:4)(cid:4) t, v (cid:5)(cid:4) t, and t (cid:4)(cid:4) s. Each Hamiltonian
G, namely the cycles
path a
[] a
s (cid:4)
275. One test case would be to count the number of strictly alternating 8
8 knight-
and-grid cycles (also known as “knight-and-wazir” cycles). Since there are 5350996 such
cycles on a 6
6 board, but only 9862 purely knight cycles, that number must be huge.
298. (a) There’s one solution for every way to cover the vertices of G by disjoint
u0
oriented cycles of length
−−→
corresponds to choosing the options ‘u−0 v0 u

(cid:4) t (cid:4)(cid:4) s; we can reject the cycles for which a > z.

v0
u1
+
−−→
1 ’, ‘u−1 v1 u

4. A cycle u0

vk
1
−
+
0 ’.
1 u

v1
u2
+
2 ’, . . . , ‘u−k
−

−−→· · · −−→
−

(b) From the 332 options, Algorithm 7.2.2.1X needs about 180 Mμ to ﬁnd 185868
9862 are the closed knight’s tours (without removing symmetries).

solutions, of which 2

1 vk

−−→

−−→

−−→

×

×

≥

(cid:7)

·

+

+

+

+

}

{

{

}

}

{

}

{

=

=

≤

≤

v1

v2

i, j

1, 2

−−−

−−−

−−−

−−−

∈ {

u1, u2

mj, ij

mj, kj

w1, w2

w1 and u2

61− 42 23

52− 44 56

or for which

= i, where m

+
1 u−2 v2 w

+
2 ’ where u1

32× 72× 56×’ and ‘41− 22 43

299. Set up an exact cover problem as in exercise 298, where n = 32 and the vertices of
the “ﬁrst part” are the cells ij with 1
8 and i + j odd. Also add primary items
ij× for i + j odd and i > 2. Each option now contains at least six items, not three:
‘u−1 v1 w
w2, the six vertices are
distinct, the i-coordinate of u1 is less than the i-coordinate of u2, and the j coordinates
of (u1, u2), (v1, v2), (w1, w2) are equal. (The u’s and w’s belong to the “ﬁrst part.”
This option represents a pair of moves with matching columns.) Furthermore, append
ij× to each option for which
and
k
. This trick forces the pairs of paths to
“hook up” properly. For example, two of the options are ‘12− 24
43×’.
16
Exploit symmetry by removing options with v1 = 11 and w1 = 32.
That makes a total of 1998 options, and Algorithm 7.2.2.1X
ﬁnds 383080 solutions in 14 Gμ. Each solution chooses 16 options,
and a good one yields a cycle (v0v1 . . . v63) in which the chosen
+
options involve v−k , vk+1, v
k+34 for k = 0, 2, . . . , 30. Most solutions
deﬁne short cyclic paths; but 5264 of them yield correct tours, such as the one shown.
300. Notice that we must have a23 = 2, a28 = 17, a47 = 18, a67 = 50, a76 = 48,
a88 = 49. To ﬁnd such a tour, we can begin by ﬁnding a knight’s path of length 14
from step 2 to step 16 that doesn’t interfere with 180◦ rotation, nor does it involve
any of the “reserved” cells. All paths of length 14 are eﬃciently found by pasting
together compatible paths of length 7. Useful paths also have the
property that each vertex in the set U of cells available for steps
2 in the graph restricted to
(18 . . 30) and (50 . . 64) has degree
U
is the set of endpoints for future
1 in that graph.
paths. The endpoints must also have degree
A similar method ﬁnds 14-step paths for steps 18 through 32 and
50 through 64. One of the 46,596 solutions is shown.

}
1 32 57 30 3 12 55 16
58 29 2 11 56 15 52 13
33 64 31 4 35 54 17 50
28 59 34 41 10 51 14 53
7 40 63 36 5 22 49 18
60 27 6 9 42 19 46 21
39 8 25 62 37 44 23 48
26 61 38 43 24 47 20 45

1 30 9 6 3 16 61 24
10 7 2 15 62 25 4 17
31 64 29 8 5 38 23 60
28 11 14 63 26 59 18 37
13 32 27 58 51 36 39 22
54 57 12 45 42 21 50 19
33 46 55 52 35 48 43 40
56 53 34 47 44 41 20 49

+
k+2, v−k+32, vk+33, v

I, where I =

47, 52, 67, 32

≥

≥

∪

{

}

December 4, 2025

(cid:12)
7.2.2.4

ANSWERS TO EXERCISES

103

301. Adapting the method in the previous exercise to paths of
other lengths, we ﬁnd that there are respectively (2, 47, 3217,
280244, 1205980, 259230, 41366) feasible solutions for the ﬁrst (4, 9,
16, 25, 36, 49, 64) steps. The ﬁrst full solution is shown. [Brentano’s
Chess Monthly 1, 1 (May 1881), 36; 1, 5 (September 1881), 248–
249. See George P. Jelliss, Mathematical Spectrum 25 (1992), 16–
20, for information about many similar “ﬁgured tours.”]

1 4 9 16 25 36 49 64
8 15 24 3 10 17 26 37
5 2 7 14 35 50 63 48
56 13 34 23 18 11 38 27
33 6 55 12 51 40 47 62
54 57 22 19 46 43 28 39
21 32 59 52 41 30 61 44
58 53 20 31 60 45 42 29

350. Let the number be Xn, and let u, v, w be the “middle” vertices on the boundary.
A Hamiltonian cycle on S
u,
where the portions from u to v, v to w, and w to u are Hamiltonian paths from corner
3
n , where Yn is the number of such paths.
to corner of S

(3)
n . Consequently Xn+1 = Y

(3)
n+1 has the form u

−−− · · · −−−

−−− · · · −−−

−−− · · · −−−

w

v

Jelliss
ﬁgured tours
Hamiltonian paths
Bradley
Teguia
Godbole
pancyclic
gallery of meander friezes
2-cycle
multigraph
Historical notes

Write uv for the corner between u and v. A Hamiltonian path from uw to vw has
vw; and there are two cases, depending
the form uw
on whether w appears before u or after v. Thus Yn+1 = ZnYnYn + YnYnZn, where
(3)
there are Zn Hamiltonian paths from corner to corner in a graph that’s like S
n but
with the third corner removed. Similarly, Zn+1 = ZnZnYn + YnZnZn + [n = 1].

−−− · · · −−−

−−− · · · −−−

−−− · · · −−−

u

v

We have (X1, Y1, Z1) = (1, 1, 1) and (X2, Y2, Z2) = (1, 2, 3). Hence, for n
3
2 Yn hold by induction.

, Yn = 3Xn, Zn =

formulas Xn = 2

n−2

n−3

+3

+3

···

3

+

3

3

1

2

3, the

≥

We can in fact write Xn = 8

[This problem was ﬁrst solved by
R. M. Bradley, J. de Physique 47 (1986), 9–14. See also A. M. Teguia and A. P.
Godbole, Australasian J. Combinatorics 35 (2006), 181–192, who showed among other
(3)
n is pancyclic: It has cycles of every length, from 3 to (3
things that S

+ 3)/2.]

12

n

·

.

n−2

(3

3)/2

−

360. (a) True. The inﬁnite rightward path that’s traced by repetitions of the patterns
will cross a vertical line once more when traveling to the right than when traveling to
the left; it will cross a horizontal line equally often when going up as when going down.
+ hn. But the

(b) The total number of edges is mn = v1 +

1 + h1 +

+ vm

left side of this equation is even, while the right side is odd by (a).

· · ·

−

· · ·

×

4a in Fig. A–30 reduces to example (iv).

(c) Frieze 5
(d) The case m = 1 is trivial. When m = 3, the only possibilities are (i)
and its cyclic shifts and/or left-right reversal; we consider them all to be equivalent
(isomorphic), although the mirror reﬂection looks diﬀerent. When m = 5 and m = 7,
there are 3 + 10 essentially distinct friezes, shown (except for (vi)) in Fig. A–30.
(e) Figure A–30 shows the 1 + 1 + 2 + 3 solutions for n = 5, 6, 7, 8.
(We need a special convention when n = 2, because the “2-cycle” C2 is a
2 meander

1. We consider ‘

’ to be a 2

multigraph with two edges 0
frieze. The 3

2a frieze reduces to it; the 2

−−−

×
4a frieze is a multiple of it.)

×
(f) The 4n automorphisms are generated by σ, τ , υ, where ijσ = i((j +1) mod n),

×

ijτ = i((

j) mod n), ijυ = (m

i)j. Notice that σ
(g, h) The equivalence class sizes (with symmetric counts in parentheses) are:

= (τ υ)

1
−

= 1.

= υ

= τ

−

−

n

2

2

2

n = 3
1 (1)
0 (0)
3 (2)
0 (0)
10 (4)

n = 4
1 (1)
3 (2)
12 (7)
30 (5)
117 (27)

n = 5
1 (1)
0 (0)
43 (12)
0 (0)
1216 (75)

n = 6
1 (1)
16 (8)
154 (35)
1152 (63)
12326 (383)

n = 7
2 (2)
0 (0)
534 (53)
0 (0)
97969 (873)

m = 3
m = 4
m = 5
m = 6
m = 7

(i) See (iii) and Fig. A–30. (Friezes 5

4d and 5

×

×

5a have only twofold symmetry.)

December 4, 2025

104

ANSWERS TO EXERCISES

7.2.2.4

4a

2

×

†‡

2a

3

×

†‡

4a

4

×

4b

4

×

†

3a

5

×

∗

3b

5

×

3c

5

×

∗

4a

5

×

∗

Jones
Chinese fretwork
fretwork
Coldstream
Dipylon Master

3a

7

×

∗

3b

7

×

3c

7

×

3d

7

×

3e

7

×

∗

3f

7

×

3g

7

×

∗

3h

7

×

3i

7

×

∗

5a

3

×

∗

6a

3

×

†

7a

3

×

∗

7b

3

×

∗

8a

3

×

∗

8b

3

×

∗

8c

3

×

†

4b

5

×

†‡

4c

5

×

†‡

4d

5

×

‡

5a

5

×

∗

4a

7

×

†‡

4b

7

×

†‡

6a

4

×

†‡

6b

4

×

†‡

6a

5

×

†‡

6b

5

×

†‡

6a

6

×

†‡

6b

6

×

†‡

6c

6

×

†‡

6a

7

×

†‡

7

6b

×

†‡

7

6c

×

†‡

Fig. A–30. A gallery of meander friezes.

6d

7

×

†‡

= 180◦ symmetry;

∗

†

= left-right symmetry;

‡

= top-bottom symmetry.

Historical notes: It’s interesting to ﬁnd instances of meander friezes in ancient
artifacts from many cultures. For example, Chapter 4 of O. Jones’s The Grammar of
Ornament (1856) included (i) as a ﬁrst example of a Greek design, and mentioned (ii)
as a related pattern found in Chinese fretwork. J. N. Coldstream’s book Greek Geo-
metric Pottery (1968), which contains detailed information about the most important
early discoveries of Greek vases from the Geometric Period, illustrates more than 40
4 frieze (v). His Plate 7 shows
specimens with the 3
3e in Fig. A–30
three ancient vases with a symmetrical 7
as (v) is related to 5

×
4 frieze, which is related to 7

3b, upside down, is in his Plate 13b.)

3 frieze (i), and six with the 5

3b. (And 5

×

×

×

The most elaborate meander frieze found so far in ancient sites is the magniﬁ-

×

×

×

4 example shown here, due to the Dipylon Master and now in the
cent 9
[See Corpus
collection of the National Archæological Museum in Athens.
Vasorum Antiquorum, Greece, Fascicule 8 (Athens, 2002), Plates 102–105.]

361. (i) 00
(ii) 00
(iii) 00
(iv) 00
(v) 00
(vi) 00
(vii) 00

01
01
01
01
01
01
03

−−−
−−−
−−−
−−−
−−−
−−−
−−−

02
11
02
11
11
11
13

−−−
−−−
−−−
−−−
−−−
−−−
−−−

03
10
03
21
21
12
10

−−−
−−−
−−−
−−−
−−−
−−−
−−−

13
20
13
22
22
13
11

−−−
−−−
−−−
−−−
−−−
−−−
−−−

23
21
12
12
02
23
21

−−−
−−−
−−−
−−−
−−−
−−−
−−−

22
22
11
02
12
03
01

−−−
−−−
−−−
−−−
−−−
−−−
−−−

12
23
21
03
13
02
02

−−−
−−−
−−−
−−−
−−−
−−−
−−−

11
13
22
13
03
22
12

−−−
−−−
−−−
−−−
−−−
−−−
−−−

21
12
23
23
23
21
22

−−−
−−−
−−−
−−−
−−−
−−−
−−−

20
02
20
20
20
20
23

−−−
−−−
−−−
−−−
−−−
−−−
−−−

10
03
10
10
10
10
20

−−−
−−−
−−−
−−−
−−−
−−−
−−−

00.
00.
00.
00.
00.
00.
00.

−−−
−−−
−−−
−−−
−−−
−−−
−−−

December 4, 2025

meander friezes
Warnsdorf’s rule
parity
Vandermonde
Historical remarks
symmetries of the cube
hyperoctahedral symmetries

3

B
Weisstein
Sticky Chain
Grabarchuk
probability distribution

7.2.2.4

ANSWERS TO EXERCISES

105

Here (i) is in P3 P4; (ii) and (iii) are the meander friezes in exercise 360; (iv)
is a multiple of the meander 3
2a; (vi) and (vii) are disjoint(!). These cycles have
respectively 2, 4, 2, 8, 4, 2, 2 automorphisms; hence their equivalence classes contribute
respectively 24, 12, 24, 6, 12, 24, 24 cycles to the total of 126 found by Algorithm H.

×

·

369. (a) For example, (000 012 110 102 121 113 011 023 103 001 022 003 123 111 013
021 002 010 112 100 020 122 101 120) is ﬁndable by hand with Warnsdorf’s rule. (And
there are 4

24 solutions altogether.)

(b) No. If so, 32 steps would take us to a cell of the opposite parity.
(c) Cells that are 32 steps apart are 110-complements.

[This remarkable cycle
was constructed by A. Vandermonde, when he introduced the concept of 3D knight’s
tours. See M´emoires Acad. Roy. Sciences (Paris, 1771), 566–574.]
023

121 together with

000

133

213

−−−

−−−

−−−

(d) S is 201

012 and 031
−−−
all eight complements of those six edges.
(e) 136656. (The total number of 4
4
there any feasible way to compute it exactly?)

−−−

−−−

×

×

4 knight’s cycles is evidently vast. Is

370. (a) Bipartiteness is obvious. Regularity is readily veriﬁed (but not obvious).

(b) The 48 symmetries of the cube all apply, leaving at most four equivalence
classes of vertices, represented by vertices
. And there are no further
{
automorphisms, because no automorphism takes any of those vertices into another: The
number of vertices at distance 2 from (000, 001, 011, 111) is respectively (16, 21, 22,
22); and 111 is at distance 2 from a corner vertex, but 011 isn’t.

000, 001, 011, 111

}

(c) (Solution by E. Weisstein.) Hamiltonian cycles are so abundant that we can
simply choose one at random, and remove it to obtain a 4-regular graph; then partition
those residual edges into two cycles. The following solution needed only a few trials:

(000 003 222 030 211 333 303 111 323 201 020 023 231 313 121 302 002 210 022 203 200 122
310 232 202 320 112 230 312 100 103 133 011 223 101 131 213 032 220 012 130 322 110 113
332 120 301 001 031 331 123 311 233 021 321 102 132 010 013 221 033 212 330 300)
(000 030 033 333 112 300 121 203 321 133 312 120 002 223 220 001 222 010 202 021 200 012
231 201 123 302 332 210 213 331 110 032 211 003 303 221 103 322 022 100 130 311 132 320
101 023 323 131 013 313 310 102 020 232 011 230 233 111 330 122 301 113 031 212)
(000 122 303 300 222 100 321 113 231 010 310 131 312 012 233 203 011 311 103 021 213 001
123 120 202 023 211 133 130 212 020 320 323 102 220 302 110 232 013 201 022 230 200 322
101 313 132 210 031 223 301 331 112 030 330 333 121 003 033 111 332 032 002 221)

[See the “Sticky Chain” puzzle in S. Grabarchuk, Age of Puzzles: Puzzle Galleries
(2019), 170, which asks for the longest path or cycle that doesn’t touch or cross itself.]

372. (a) One billion trials yield the following interesting probability distribution:

k =

2 4 6 8 10 12 14 16 18 20 22 24 26 28 30 32 34 36 38 40 42 44 46 48 50 52 54 56 58 60 62 64

4%

3%

2%

1%

0%

have probabilities

(b) The ten essentially diﬀerent ﬁnal squares (00, 01, 02, 03; 11, 12, 13; 22, 23; 33)
(.0845, .0369, .0118, .0216; .0123, .0005, .0030; .0002, .0009; .0035).
(c) When k is even, the probability of a k-cycle has been “hollowed out” in the
histogram above. The exact totals, in the billion trials used for this illustration, were
595532 when k = 4 (all cycles) and 157 when k = 64 (17 cycles).

≈

December 4, 2025

106

ANSWERS TO EXERCISES

7.2.2.4

[Wolf carried out 1000 experiments by hand, each taking less than 15 minutes
on average, and described them in admirable detail in a posthumous contribution to
the Vierteljahrsschrift der naturforschenden Gesellschaft in Z¨urich 39 (1894), 147–164.
Not surprisingly, however, his tables contained dozens of typographic and/or parity
errors. Note that the probability of ending with k = 4 is exactly 1/1680. Is it feasible to
calculate the exact probability distribution for all k, with something like Algorithm E?]
999. . . .

historical note
parity

December 4, 2025

APPENDIX E

ANSWERS TO PUZZLES IN THE ANSWERS

n00 R21 q11 K20 r31 Q41 r42 R40 k44 B34 q12 B02 r35 Q25 b45 R23 n43 K24 n33 B14 b32 N10
k22 N13 q01 K04 k05 N15 b03 Q30 n00

(see answer 220)

B00 N33 K12 N23 R02 N32 K13 N22 B03 N30 K11 N20 Q01 N31 K10 N21 B00

(see answer 221)

December 4, 2025

107

INDEX AND GLOSSARY

Florus, Lucius

Read the table that follows, my honest reader,
and it will soon guide you to hold the entire work in your mind.

— Lucii Flori Bellorum Romanorum libri quattuor (Vienna, 1511)

When an index entry refers to a page containing a relevant exercise, see also the answer to
that exercise for further information. An answer page is not indexed here unless it refers to a
topic not included in the statement of the exercise.

2-factor, see Cycle cover.
Articulation point: A vertex whose

removal increases the number of
components of a graph.

Barry, David McAlister (= Dave), iii.
Biconnected graph: A graph without

articulation points.

Cycle cover: A covering of the vertices by

disjoint cycles (a 2-regular spanning
subgraph, if undirected).

FGbook: Selected Papers on Fun & Games,

a book by D. E. Knuth.

Hamiltonian graph: A graph with a

spanning cycle, 2.

Oni,tiu, Valeriu (= Valerian).

Nothing else is indexed yet (sorry).

Preliminary notes for indexing appear in the
upper right corner of most pages.

Cyclically k-connected: Must remove at

If I’ve mentioned somebody’s name and

least k edges to obtain two cyclic
(nontree) components.

forgotten to make such an index note,
it’s an error (worth $2.56).

December 4, 2025

108


