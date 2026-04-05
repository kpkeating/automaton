intrinsic GetPoly(S::{}) -> RngMPolElt
{Given a generating set S for an ideal I in a polynomial ring in 4
variables, this function attempts to find an element f in a
Groebner basis for I which depends only on the last two variables
t,X.  It then tries to find an irreducible factor g of f which has
a solution of the form X=t+a_1t^2+... .  The function returns an
error message if there is no such factor, or more than one.
Otherwise it returns g.}
   R:=Parent(Random(S));
   I:=Ideal(S);
   Ielim:=ChangeOrder(I,"elim",2);
   G:=GroebnerBasis(Ielim);
   n:=#G;
   felim:=G[n];
   f:=R!felim;
   f00:=Evaluate(f,[0,0,R.3,R.4]);
   error if f00 ne f, "Input Polynomial depends on y or a3.";
   factors:=Factorization(f);
   winner:=R!0;
   for pair in factors do
      g:=pair[1];
      mindegree:=Minimum({Degree(term):term in Terms(g)});
      if mindegree ne 0 then
         minterms:={term:term in Terms(g) | Degree(term) eq mindegree};
         gmin:=R!0;
         for term in minterms do
            gmin:=gmin+term;
         end for;
         gmin11:=Evaluate(gmin,[0,0,1,1]);
         if gmin11 eq 0 then
            error if winner ne 0, g,winner,"are both factors.";
            winner:=g;
         end if;
      end if;
   end for;
   error if winner eq 0,"Couldn't find a polynomial of the correct form.";
   return winner;
end intrinsic;

intrinsic CartierOp(f::.,r::RngIntElt,q::RngIntElt) -> .
{This function applies the Cartier-like operator \Lambda_r to the
polynomial f with coefficients in a finite field, where r is
taken from 0,1,...,q-1.  It is used by the function AutomatonDiag.}
   S:=Parent(f);
   F:=CoefficientRing(S);
   if Type(S) eq RngUPol then
      R:=PolynomialRing(F,1);
      g:=Evaluate(f,R.1);
   else
      R:=S;
      d:=Rank(R);
      vars:=[];
      for i in [1..d] do
         Append(~vars,R.i);
      end for;
      g:=Evaluate(f,vars);
   end if;
   d:=Rank(R);
   //q:=#F;
   C:=Coefficients(g);
   M:=Monomials(g);
   n:=#C;
   Crg:=R!0;
   Z:=IntegerRing();
   for i in [1..n] do
      rems:=[(Z!0)^^d];
      for j in [1..d] do
         rems[j]:=Degree(M[i],j) mod q;
      end for;
      if rems eq [(Z!r)^^d] then
         newterm:=C[i];
         for j in [1..d] do
            newexp:=(Degree(M[i],j)-r)div q;
            newterm:=newterm*R.j^newexp;
         end for;
         Crg:=Crg+newterm;
      end if;
   end for;
   if Type(S) eq RngUPol then
      Crg:=Evaluate(Crg,[S.1]);
   end if;
   return Crg;
end intrinsic;

intrinsic AutomatonDiag(G::RngMPolElt,q::RngIntElt,n::RngIntElt) ->
Mtrx,RngIntElt,RngIntElt,RngIntElt
{This function takes as input a polynomial G(t,X) in two variables
over a finite field F, produced, for instance, by the "GetPoly"
function.  G must be be "nonsingular", meaning that G(0,0)=0 and
G_X(0,0) is nonzero.  The function computes an automaton whose
output is a series phi such that of G(t,phi): It returns a matrix
M which gives the digraph structure and edge labels of the
automaton, and a column vector L which gives the state labels of
the automaton.  The digraph is constructed using a breadth-first
search.  The input q is the size of the input alphabet of the
automaton; it should be a power of the characteristic of F.
The input n gives a limit on the depth of the search.  The
output m is the number of states in the automaton, and d is the
distance from the start vertex to the furthest vertex.}
   R:=Parent(G);
   F:=CoefficientRing(R);
   //q:=#F;
   r:=Rank(R);
   S:=PolynomialRing(F,2);
   GS:=Evaluate(G,[0^^(r-2),S.1,S.2]);
   error if Evaluate(GS,[0,0]) ne 0, "Polynomial is singular since G(0,0) is nonzero.";
   c:=Evaluate(Derivative(GS,2),[0,0]);
   error if c eq 0, "Polynomial is singular since G_X(0,0)=0.";
   Q:=Evaluate(GS,[S.1*S.2,S.2]) div (c*S.2);
   P0:=Derivative(GS,S.2) div c;
   P:=S.2*Evaluate(P0,[S.1*S.2,S.2]);
   V:={P};
   C:={P};
   Z:=IntegerRing();
   M:=Matrix(Z,0,q,[]);
   L:=Matrix(F,1,1,[0]);
   Index:=AssociativeArray();
   Index[P]:=1;
   h:=1;
   for i in [0..n] do
      d:=i;
      N:=[];
      for f in C do
         newrow:=Matrix(Z,1,q,[0^^q]);
         for j in [0..q-1] do
            new:=CartierOp(f*Q^(q-1),j,q);
            if new notin V then
               Append(~N,new);
               V:=V join {new};
               zvmat:=Matrix(F,1,1,[Evaluate(new,[0,0])]);
               L:=VerticalJoin(L,zvmat);
               h:=h+1;
               Index[new]:=h;
            end if;
            newrow[1,j+1]:=Index[new];
         end for;
         M:=VerticalJoin(M,newrow);
      end for;
      C:=N;
      if N eq [] then
         break;
      end if;
   end for;
   m:=NumberOfRows(M);
   error if #C ne 0, "There are",#C,"active vertices.",M,L,m,d;
   return M,L,m,d;
end intrinsic;

intrinsic LambdaCartier(eta::DiffCrvElt,m::RngIntElt) -> .
{This function iteratively applies the Cartier operator to
differential forms on a fixed curve over the finite field F_q,
where q=p^r.  It is used by the AutomatonCartier function.}
   C:=Curve(eta);
   A2:=AmbientSpace(C);
   R:=CoordinateRing(A2);
   F:=CoefficientRing(R);
   q:=#F;
   qfact:=Factorization(q);
   p:=qfact[1][1];
   r:=qfact[1][2];
   output:=eta;
   rem:=m;
   K:=FunctionField(C);
   for i in [1..r] do
      h:=rem mod p;
      output:=Cartier(K.1^(p-1-h)*output);
      rem:=(rem-h) div p;
   end for;
   return output;
end intrinsic;

intrinsic AutomatonCartier(G::RngMPolElt,n::RngIntElt)
-> Mtrx,RngIntElt,RngIntElt,RngIntElt
{This function takes as input a polynomial G(t,X) in two variables
over a finite field F, produced, for instance, by the "GetPoly"
function.  It returns a matrix M which gives the digraph structure
and edge labels of an automaton which corresponds to a solution to
G(t,X)=0.  The digraph is constructed using a breadth-first
search; the input n gives a limit on the depth of the search.  The
output m is the number of vertices in the automaton, and d is the
distance from Start to the furthest vertex.  If G is nonsingular
then the vertex labels can be computed using the LabelsFromPoly
function.}
   R:=Parent(G);
   F:=CoefficientRing(R);
   q:=#F;
   facq:=Factorization(q);
   p:=facq[1][1]; d:=facq[1][2];
   r:=Rank(R);
   S:=PolynomialRing(F,2);
   GS:=Evaluate(G,[0^^(r-2),S.1,S.2]);
   A2:=AffineSpace(F,2);
   C:=Curve(A2,GS);
   K:=FunctionField(C);
   w:=K.2*Differential(K.1);
   V:={w};
   C:={w};
   Z:=IntegerRing();
   M:=Matrix(Z,0,q,[]);
   Index:=AssociativeArray();
   Index[w]:=1;
   h:=1;
   for i in [1..n] do
      d:=i-1;
      N:=[];
      for eta in C do
         newrow:=Matrix(Z,1,q,[0^^q]);
         for j in [0..q-1] do
            new:=LambdaCartier(eta,j);
            if new notin V then
               Append(~N,new);
               V:=V join {new};
               h:=h+1;
               Index[new]:=h;
            end if;
            newrow[1,j+1]:=Index[new];
         end for;
         M:=VerticalJoin(M,newrow);
      end for;
      C:=N;
      if N eq [] then
         break;
      end if;
   end for;
   m:=NumberOfRows(M);
   return M,m,d,#C;
end intrinsic;

intrinsic OreMultiple(f::RngUPolElt,q::RngIntElt) -> .
{This function returns the q-Ore polynomial of smallest degree
which is divisible by f.  The input f should be a polynomial over
an integral domain of characteristic p, and q should be a power of
p.}
   A:=Parent(f);
   R:=CoefficientRing(A);
   n:=Degree(f);
   fcoeffs:=Coefficients(f);
   qpowers:={1};
   for i in [1..n] do
      qpowers:=qpowers join {q^i};
   end for;
   M:=ZeroMatrix(R,q^n-n,q^n);
   for j in [1..q^n] do
      if j notin qpowers then
         for h in [0..n] do
            i:=j-h;
            if i in [1..q^n-n] then
               M[i,j]:=fcoeffs[h+1];
            end if;
         end for;
      end if;
   end for;
   N:=Nullspace(M);
   B:=Basis(N);
   orefactor:=B[1];
   poly:=A!0;
   for i in [1..q^n-n] do
      poly:=poly+orefactor[i]*A.1^i;
   end for;
   orepoly:=f*poly;
   return orepoly;
end intrinsic;

intrinsic OreCoeffs(f::.,q::RngIntElt) -> []
{This function returns a sequence whose terms are the coefficients
of the q-Ore polynomial f.}
   R:=Parent(f);
   n:=Degree(f);
   fcoeffs:=Coefficients(f);
   qpowers:={};
   i:=0;
   while q^i le n do
      qpowers:=qpowers join {q^i};
      i:=i+1;
   end while;
   orecoeffs:=[];
   for i in [0..n] do
      if i in qpowers then
         Append(~orecoeffs,fcoeffs[i+1]);
      else
         error if fcoeffs[i+1] ne 0, "Input is not in Ore form.";
      end if;
   end for;
   return orecoeffs;
end intrinsic;

intrinsic LambdaOre(D::[],B::[],r::RngIntElt) -> .
{This function iteratively applies the function CartierOp to Ore
polynomials.  It is used by the AutomatonOre function.}
   R:=Parent(B[1]);
   F:=CoefficientRing(R);
   q:=#F;
   d:=#B-1;
   LrD:=[(R!0)^d];
   Append(~D,0);
   Append(~B,0);
   for k in [1..d] do
      LrD[k]:=CartierOp(D[k+1]-D[1]*B[k+1]*B[1]^(q^k-2),r);
   end for;
   return LrD;
end intrinsic;

intrinsic AutomatonOre(G::RngMPolElt,n::RngIntElt) -> Mtrx,RngIntElt
{This function takes as input a polynomial G(t,X) in two variables
over a finite field F, produced, for instance, by the GetPoly
function.  It returns a matrix M which gives the digraph structure
and edge labels of an automaton which corresponds to a solution to
G(t,X)=0.  The digraph is constructed using a breadth-first
search; the input n gives a limit on the depth of the search.  The
output m is the number of vertices in the automaton, and d is the
distance from Start to the furthest vertex.  If G is nonsingular
then the vertex labels can be computed using the LabelsFromPoly
function.}
   R:=Parent(G);
   F:=CoefficientRing(R);
   q:=#F;
   FT:=PolynomialRing(F);
   FTX:=PolynomialRing(FT);
   GG:=Evaluate(G,[0,0,FT.1,FTX.1]);
   GOre:=OreMultiple(GG,q);
   B:=OreCoeffs(GOre,q);
   d:=#B-1;
   R:=Parent(B[1]);
   s0:=[B[1],(R!0)^^(d-1)];
   V:={s0};
   C:={s0};
   Z:=IntegerRing();
   M:=Matrix(Z,0,q,[]);
   Index:=AssociativeArray();
   Index[s0]:=1;
   h:=1;
   for i in [0..n] do
      d:=i;
      N:=[];
      for D in C do
         newrow:=Matrix(Z,1,q,[0^^q]);
         for r in [0..q-1] do
            new:=LambdaOre(D,B,r);
            if new notin V then
               Append(~N,new);
               V:=V join {new};
               h:=h+1;
               Index[new]:=h;
            end if;
            newrow[1,r+1]:=Index[new];
         end for;
         M:=VerticalJoin(M,newrow);
      end for;
      C:=N;
      if C eq [] then
         break;
      end if;
   end for;
   m:=NumberOfRows(M);
   return M,m,d,#C;
end intrinsic;

intrinsic AutomatonOutput(M::Mtrx,tuple::Tup:L:=[]) -> []
{This function computes the vertex v at the end of the path
determined by the input tuple in the edge-labelled digraph given
by the matrix M.  If a vector L of labels is specified, the
function returns the label of v.  If not, the function returns
v.}
   n:=#tuple;
   v:=1;
   for i in [1..n] do
      v:=M[v,tuple[i]+1];
   end for;
   if L eq [] then
      return v;
   else
      return L[v];
   end if;
end intrinsic;

intrinsic VertLabels(M::Mtrx,phi::RngSerElt) -> Mtrx
{This function returns the column vector of labels for the
automaton with matrix M associated to the series phi(t).  The
series phi(t) must be specified with precision t^(q^d) to
guarantee success, where d is the depth of the digraph given by
M.}
   n:=NumberOfRows(M);
   R:=Parent(phi);
   F:=CoefficientRing(R);
   q:=#F;
   L:=ZeroMatrix(F,n,1);
   done:={1};
   prec:=Precision(phi);
   error if Type(prec) eq Infty, "Input series must have finite precision.";
   top:=Ceiling(Log(q,prec-1));
   for d in [1..top] do
      tuples:=CartesianPower([0..q-1],d);
      for t in tuples do
         sum:=0;
         for i in [1..d] do
            sum:=sum+t[i]*q^(i-1);
         end for;
         if sum lt prec then
            v:=AutomatonOutput(M,t);
            c:=Coefficient(phi,sum);
            if v in done then
               error if c ne L[v,1], "State",v,"is inconsistently labeled.";
            else
               L[v,1]:=c;
               done:=done join {v};
            end if;
         end if;
      end for;
   end for;
   undone:={1..n} diff done;
   error if undone ne {},L,"States",undone,"have not been labeled.";
   return L;
end intrinsic;

intrinsic LabelsFromPoly(G::RngMPolElt,M::Mtrx,d::RngIntElt) -> Mtrx
{This function computes the column vector of labels for the
automaton with matrix M associated to a series which is a root of
G(t,X).  It can be used in conjunction with AutomatonCartier or
AutomatonOre.}
   R:=Parent(G);
   F:=CoefficientRing(R);
   q:=#F;
   A:=PowerSeriesRing(F);
   AX:=PolynomialRing(A);
   GAX:=Evaluate(G,[0,0,A.1,AX.1]);
   phi:=ImplicitFunction(GAX,1,q^d);
   L:=VertLabels(M,phi);
   return L;
end intrinsic;

intrinsic Series(M::Mtrx,L::Mtrx,n::RngIntElt) -> RngSerElt
{This function returns the series phi(t) determined by the
automaton defined by the pair M,L, up to precision t^n.}
   F:=Parent(L[1,1]);
   R:=PowerSeriesRing(F);
   series:=R!0;
   q:=#F;
   for i in [1..n-1] do
      h:=i;
      tuple:=<>;
      while h ne 0 do
         Append(~string,h mod q);
         h:=h div q;
      end while;
      v:=AutomatonOutput(M,string);
      c:=L[v,1];
      series:=series+c*(R.1)^i;
   end for;
   return series+O(R.1^n);
end intrinsic;
