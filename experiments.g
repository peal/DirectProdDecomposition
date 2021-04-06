# Code to reproduce the experiments from 'Disjoint direct product decompositions of permutation groups'
# By Mun See Chang and Christopher Jefferson


Read("DDPD.g");
Read("Miller.g");
LoadPackage("io");


# EXP := 1,2,3,4,5 or 6

if not IsBound(EXP) then
    Error("Must define 'EXP' to choose which Experiment to run (1,2,3,4,5 or 6)");
fi;


cleanGroup := function(g)
    local s;
    s := Size(g);
    g := Group(GeneratorsOfGroup(g),());
    SetSize(g,s);
    return g;
end;

RestrictedGroup := function(g, l)
    return Group(List(GeneratorsOfGroup(g), x -> RestrictedPerm(x,l)), Identity(g));
end;

CheckGroup := function(grp, max2, ingrp)
    local pnts, a, b, c;
    pnts := LargestMovedPoint(ingrp);
    a := Length(DDPD(grp));
    b := List([0..max2-1], px -> Size(RestrictedGroup(grp, [pnts*px+1..pnts*(px+1)])));
    return a = 1 and ForAll(b, x -> x = Size(ingrp));
end;

mkGroup := function(ingrp, max1, max2)
    local grp, grplist, g, i;
    i := 0;
    grplist := [];
    while i < max1 do
        g := DirectProduct(List([1..max2], x -> ingrp));
        g := Group(List([1..Random([1..max2])], x -> Random(g)));
        if CheckGroup(g, max2, ingrp) then
            g := g^(Random(SymmetricGroup(LargestMovedPoint(g))));
            g := cleanGroup(g);
            Add(grplist, g);
            i := i + 1;
        fi;
    od;
    grp := DirectProduct(grplist);
    grp := grp^Random(SymmetricGroup(LargestMovedPoint(grp)));
    grp := cleanGroup(grp);
    return [grplist, grp];
end;

timeFunction := function(func)
    local a1,a2, ret;
    a1 := NanosecondsSinceEpoch();
    ret := CallFuncList(func, []);
    a2 := NanosecondsSinceEpoch();
    return [a2-a1, ret];
end;


timeStep := function(func, ingrp, max1, max2)
    local g, i, t1, t2, ret, grp, grplist, p1, p2, s, decompTime;
    p1 := []; p2 := []; decompTime := [];
        ret := mkGroup(ingrp, max1, max2);
        grplist := ret[1];
        grp := ret[2];
        
        ret := timeFunction({} -> func(grp));
        grp := cleanGroup(grp);

        ret := timeFunction({} -> DDPD(grp));
        grplist := List(grplist, cleanGroup);

        ret :=  timeFunction({} -> List(grplist, func));

end;

timedirect := function(func, ingrp, max1, max2)
    local g, i, t1, t2, ret, grp, grplist, p1, p2, s, decompTime;
    p1 := []; p2 := []; decompTime := [];
    for i in [1..10] do
        ret := mkGroup(ingrp, max1, max2);
        grplist := ret[1];
        grp := ret[2];
        
        ret := IO_CallWithTimeout(rec(minutes := 10), timeFunction, {} -> func(grp));
        if ret[1] = true then
            Add(p1, ret[2][1]);
        fi;

        grp := cleanGroup(grp);

        ret := IO_CallWithTimeout(rec(minutes := 10), timeFunction, {} -> DDPD(grp));
        if ret[1] = true then
            Add(decompTime, ret[2][1]);
        fi;

        grplist := List(grplist, cleanGroup);

        ret := IO_CallWithTimeout(rec(minutes := 10), timeFunction, {} -> List(grplist, func));
        if ret[1] = true then
            Add(p2, ret[2][1]);
        fi;
    od;

    Sort(p1);
    Sort(decompTime);
    Sort(p2);
    # Print(grp, ":", grplist, ":", a1, ":", a2, "\n");
    return rec(full := p1, parts := p2, decompTime := decompTime, s := Size(grp));
end;

#minnorm := timedirect(MinimalNormalSubgroups, AlternatingGroup(5), 10);
#Print(minnorm,"\n");

PreTable := function()
    Print("\\begin{tabular}{|c|c|c|c|c|c|c|c|c|}\n");
    Print("\\hline\n");
    Print("Group&cpy&parts&Full&Full(Count)&Parts&Parts(Count)&Decomposition&Decomp(Count)\\\\\n");
    Print("\\hline\n");
end;

EndTable := function()
    Print("\\hline\n");
    Print("\\end{tabular}\n");
end;

timered := (1000*1000*1000)/100;

DotNum := function(num)
    local s;
    s := String(Int(num/timered));
    if Length(s) = 1 then
        return StringFormatted("0.0{}", s);
    elif Length(s) = 2 then
        return StringFormatted("0.{}", s);
    else
        return StringFormatted("{}.{}", s{[1..Length(s)-2]}, s{[Length(s)-1..Length(s)]});
    fi;
end;


SafeMedian := function(l)
    l := SortedList(l);
    if Length(l) < 5 then
        return "N/A";
    else
        return DotNum(l[5]);
    fi;
end;

PrintLine := function(g, i, j, r)
#Print(r);
    PrintFormatted("{} & {} & {} & {} & {} & {} & {} & {} & {} \\\\\n", g,i,j,SafeMedian(r.full), Length(r.full), SafeMedian(r.parts), Length(r.parts), SafeMedian(r.decompTime), Length(r.decompTime));
end;

MinimalNormalSubgroupsNoReply := function(g)
    MinimalNormalSubgroups(g);
    return 0;
end;

CompositionSeriesNoReply := function(g)
    CompositionSeries(g);
    return 0;
end;

if EXP = 1 then
PreTable();
for i in [6,8,10,12,14,16,18,20] do
cyclic := timedirect(DerivedSubgroup, SymmetricGroup(4), i,4);
PrintLine("S4",i,4,cyclic);
cyclic := timedirect(DerivedSubgroup, AlternatingGroup(4), i,4);
PrintLine("A4",i,4,cyclic);
cyclic := timedirect(DerivedSubgroup, DihedralGroup(IsPermGroup, 8), i,4);
PrintLine("D8",i,4,cyclic);
cyclic := timedirect(DerivedSubgroup, DihedralGroup(IsPermGroup, 32), i,4);
PrintLine("D32",i,4,cyclic);
cyclic := timedirect(DerivedSubgroup, TransitiveGroup(16,712), i,4);
PrintLine("Trans(16,712)",i,4,cyclic);
cyclic := timedirect(DerivedSubgroup, TransitiveGroup(16,713), i,4);
PrintLine("Trans(16,713)",i,4,cyclic);
od;
EndTable();
elif EXP = 2 then
PreTable();
for i in [2..6] do
conjclass := timedirect(NrConjugacyClasses, AlternatingGroup(3), i,4);
PrintLine("A3",i,4,conjclass);
od;
for i in [2..6] do
conjclass := timedirect(NrConjugacyClasses, SymmetricGroup(4), i,4);
PrintLine("S4",i,4,conjclass);
od;
for i in [2..6] do
conjclass := timedirect(NrConjugacyClasses, DihedralGroup(IsPermGroup, 8), i,4);
PrintLine("D8",i,4,conjclass);
od;
for i in [2..6] do
conjclass := timedirect(NrConjugacyClasses, DihedralGroup(IsPermGroup, 32), i,4);
PrintLine("D32",i,4,conjclass);
od;
for i in [2..6] do
conjclass := timedirect(NrConjugacyClasses, TransitiveGroup(16,712), i,4);
PrintLine("Trans(16,712)",i,4,conjclass);
od;
for i in [2..6] do
conjclass := timedirect(NrConjugacyClasses, TransitiveGroup(16,713), i,4);
PrintLine("Trans(16,713)",i,4,conjclass);
od;
EndTable();
elif EXP = 3 then

PreTable();
for i in [2,4..10] do
conjclass := timedirect(MinimalNormalSubgroupsNoReply, SymmetricGroup(4), i,4);
PrintLine("S4",i,4,conjclass);
od;
for i in [2,4..10] do
conjclass := timedirect(MinimalNormalSubgroupsNoReply, AlternatingGroup(4), i,4);
PrintLine("A4",i,4,conjclass);
od;
for i in [2,4..10] do
conjclass := timedirect(MinimalNormalSubgroupsNoReply, DihedralGroup(IsPermGroup, 8), i,4);
PrintLine("D8",i,4,conjclass);
od;
for i in [2,4..10] do
conjclass := timedirect(MinimalNormalSubgroupsNoReply, DihedralGroup(IsPermGroup, 32), i,4);
PrintLine("D32",i,4,conjclass);
od;
for i in [2,4..10] do
conjclass := timedirect(MinimalNormalSubgroupsNoReply, TransitiveGroup(16,712), i,4);
PrintLine("Trans(16,712)",i,4,conjclass);
od;
for i in [2,4..10] do
conjclass := timedirect(MinimalNormalSubgroupsNoReply, TransitiveGroup(16,713), i,4);
PrintLine("Trans(16,713)",i,4,conjclass);
od;
EndTable();

elif EXP = 4 then
PreTable();
for i in [2,3,4] do
conjclass := timedirect(StructureDescription, SymmetricGroup(4), i,4);
PrintLine("S4",i,4,conjclass);
conjclass := timedirect(StructureDescription, AlternatingGroup(4), i,4);
PrintLine("A4",i,4,conjclass);
conjclass := timedirect(StructureDescription, DihedralGroup(IsPermGroup, 8), i,4);
PrintLine("D8",i,4,conjclass);
conjclass := timedirect(StructureDescription, DihedralGroup(IsPermGroup, 32), i,4);
PrintLine("D32",i,4,conjclass);
conjclass := timedirect(StructureDescription, TransitiveGroup(16,712), i,4);
PrintLine("Trans(16,712)",i,4,conjclass);
conjclass := timedirect(StructureDescription, TransitiveGroup(16,713), i,4);
PrintLine("Trans(16,713)",i,4,conjclass);
od;
EndTable();
elif EXP = 5 then
PreTable();
for i in [4,8..20] do
conjclass := timedirect(CompositionSeriesNoReply, SymmetricGroup(4), i,4);
PrintLine("S4",i,4,conjclass);
conjclass := timedirect(CompositionSeriesNoReply, AlternatingGroup(4), i,4);
PrintLine("A4",i,4,conjclass);
conjclass := timedirect(CompositionSeriesNoReply, DihedralGroup(IsPermGroup, 8), i,4);
PrintLine("D8",i,4,conjclass);
conjclass := timedirect(CompositionSeriesNoReply, DihedralGroup(IsPermGroup, 32), i,4);
PrintLine("D32",i,4,conjclass);
conjclass := timedirect(CompositionSeriesNoReply,TransitiveGroup(16,712), i,4);
PrintLine("Trans(16,712)",i,4,conjclass);
conjclass := timedirect(CompositionSeriesNoReply,TransitiveGroup(16,713), i,4);
PrintLine("Trans(16,713)",i,4,conjclass);
od;
EndTable();
elif EXP = 6 then
PreTable();
for i in [12,14..30] do
cyclic := timedirect(DDPDAlt, SymmetricGroup(4), i,4);
PrintLine("S4",i,4,cyclic);
cyclic := timedirect(DDPDAlt, AlternatingGroup(4), i,4);
PrintLine("A4",i,4,cyclic);
cyclic := timedirect(DDPDAlt, DihedralGroup(IsPermGroup, 8), i,4);
PrintLine("D8",i,4,cyclic);
cyclic := timedirect(DDPDAlt, DihedralGroup(IsPermGroup, 32), i,4);
PrintLine("D32",i,4,cyclic);
cyclic := timedirect(DDPDAlt, TransitiveGroup(16,712), i,4);
PrintLine("Trans(16,712)",i,4,cyclic);
cyclic := timedirect(DDPDAlt, TransitiveGroup(16,713), i,4);
PrintLine("Trans(16,713)",i,4,cyclic);
od;
EndTable();
fi;

