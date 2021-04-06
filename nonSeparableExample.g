# example of a digraph where the strong generating set outputted from nauty is not separable
# This provides a counter-example to a conjecture in 'On the constructive orbit problem'
# by Donaldson A.F. and Miller A.

 

LoadPackage( "NautyTracesInterface" );
LoadPackage( "Grape" );
LoadPackage( "Digraph" );

 

###################################################################################
#these are some concrete examples

 

G:=Group([ (1,3,2)(4,5,6)(10,12,11), (1,3,2)(7,8,9) ]);
c:= Random(SymmetricGroup(LargestMovedPoint(G)));
G:=G^c;

 

G:=Group([ (1,3,2)(4,6,5)(7,9,8)(10,11,12), (1,2,3)(10,11,12) ]);
c:= Random(SymmetricGroup(LargestMovedPoint(G)));
G:=G^c;

 

G:=Group([ (6,7,8,9,10)(11,12,13,14,15),(1,2,3,4,5)(6,7,8,9,10)(11,12,13,14,15) ]);
c:= Random(SymmetricGroup(LargestMovedPoint(G)));
G:=G^c;

 

###################################################################################
#alternatively one could look for more examples by varying numOfHOrbits, numOfRows and p;

 

numOfHOrbits:=4;
numOfRows:=2;
p:=5;

 

basisVecs:= List([1..numOfRows], y->List([1..numOfHOrbits], x-> Random([0..p-1]) ));
genOfH:=[];
for vec in basisVecs do
  gen:=();
  for posn in [1..numOfHOrbits] do
    for entryNum in [1..p-1] do
      if vec[posn]=entryNum then
        gen:=gen*CycleFromList( [p*(posn-1)+1..p*posn])^entryNum;
      fi;
    od;
  od;
  Add(genOfH,gen);
od;

 

G:=Group(genOfH);
c:= Random(SymmetricGroup(LargestMovedPoint(G)));
G:=G^c;

 

###################################################################################

 

vertices:= [1..LargestMovedPoint(G)];
edges:=[];
seenEdges:=[];

 

for i in [1..LargestMovedPoint(G)] do
  for j in [1..LargestMovedPoint(G)] do
    if not [i,j] in seenEdges then
      Add(edges, Orbit(G, [i,j], OnPairs));
      seenEdges:= Union(edges);
    fi;
  od;
od;

 

edgesList:=[];
source:=[];
range:=[];
for edgeSet in edges do
  store:= Length(vertices)+1;
  Add(vertices, store);
  for edge in edgeSet do
    Add(vertices, Length(vertices)+1);
    Add(source, edge[1]);
    Add(range, Length(vertices));
    Add(source, Length(vertices));
    Add(range, edge[2]);
    Add(source, store);
    Add(range, Length(vertices));
    Add(source, Length(vertices));
    Add(range, store);
  od;
od;
digraph:= Digraph(vertices, source, range);
AutC:=NautyAutomorphismGroup(digraph);
#AutC:=AutomorphismGroup(digraph);

 


#colorVertices  := Filtered(vertices, x-> not x in [1..LargestMovedPoint(G)]);
#Aut:= Stabilizer(AutC, colorVertices, OnSets);

 

#N:=Normaliser(SymmetricGroup(LargestMovedPoint(G)),G);
#orbsN:= StructuralCopy(Orbits(N));
#Size(N)=Size(Action(N, orbsN[1], OnPoints))*Size(Action(N, orbsN[2], OnPoints));

 


#A:=Action(Aut, [1..LargestMovedPoint(G)]);
#orbsA:= StructuralCopy(Orbits(A));
#Size(A)=Size(Action(A, orbsA[1], OnPoints))*Size(Action(A, orbsA[2], OnPoints));

 


Pgens:=List(GeneratorsOfGroup(AutC), gen-> RestrictedPerm(gen, [1..LargestMovedPoint(G)]));
P:=Group(Pgens);
orbsP:= StructuralCopy(Orbits(P));
isfullDP:= Size(P)= Product(List([1..Length(orbsP)], x-> Size(Action(P, orbsP[x], OnPoints))));

 

Print("orbsPNum ", Length(orbsP), ",");
Print("isfullDP ", isfullDP, ",");

 

isSeparable:=true;
for gen in Pgens do
  first:=true;
  for orb in orbsP do
    if Length(Intersection(MovedPoints(gen), orb))>0 then
      if first=true then
        first:=false;
      else
        isSeparable:=false;
        Print("gen: ", gen);
        break;
      fi;
    fi;
  od;
od;

 

Print("isSeparable: ", isSeparable, "\n");