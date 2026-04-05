The Magma package AutomatonPack.m is meant to help compute
finite automata which determine the coefficient sequences
of elements of the Nottingham group with finite order, as
described in the paper

K. Keating, Some nonabelian subgroups of the Nottingham
group over F_4.


The function GetPoly(S) attempts to deduce a polynomial relation
between t and X from the relations among \alpha_3, Y, t, and X
specified in S.

AutomatonDiag(G,n) uses Furstenberg's diagonal method to compute a
finite automaton which determines the coefficients of a series
which is a root of the polynomial G.  It returns an error message
if G is "singular".  The input n specifies a limit on the depth of
the breadth-first search used in the computation.

AutomatonCartier(G,n) uses the Cartier operator to compute the
digraph structure and edge labels of an automaton which determines
the coefficients of a series which is a root of G.

AutomatonOre(G,n) also computes the digraph structure and edge
labels of our automaton, in this case using Ore polynimials.


Here is an example which computes the automaton for
\sigma_1(t), as described in Section 7 of the paper:

> Attach("AutomatonPack.m");
> F4<s>:=GF(4);
> R<Y,a3,t,X>:=PolynomialRing(F4,4);
> S:={a3^2-a3-Y^3,t*a3-Y,(a3+s^2*Y+s^2)*X-Y-s};
> f:=GetPoly(S);
> f;
t^2*X^2 + s*t^2 + X^2 + t + X
> M,L:=AutomatonDiag(f,4,10);
> // The input 4 gives the size of the input alphabet.
> // The input 10 is a bound on the depth of the search used to
> // construct the automaton.  If this number is set too small the
> // program terminates with an error message.  There is no time
> // penalty if it is set larger than necessary.
> M;
[2 3 4 5]
[2 6 7 4]
[3 5 5 5]
[6 8 7 4]
[5 5 5 5]
[6 6 7 4]
[8 8 7 4]
[8 6 7 4]
> L;
[  0]
[  0]
[  1]
[s^2]
[  0]
[s^2]
[  s]
[  s]

