# The function 'DDPDAlt' gives the finest disjoint direct product decomposition of a permutation
# group G, as described in 'On the constructive orbit problem' by Donaldson A.F. and Miller A.

sizeProjectOrb := {g, o} -> Size(Group(List(GeneratorsOfGroup(g), x -> RestrictedPerm(x,o)),()));

DDPDAlt := function(G)
    local timerec, orbits, sizes, mergedorbits, tryMergeOrbit, o, baseorblist, finalorblist, doSplit;

    timerec := rec();
    orbits := Orbits(G);
    if IsTrivial(G) then
	    return [rec(base := [], genset := [()], group := Group(()))];
    fi;
    if Size(orbits) = 1 then
        # We were given a transitive group!
        return [rec(base :=  BaseStabChain(StabChain(G)), genset := GeneratorsOfGroup(G), group := G)];
    fi;

    # Make function always produce same ordered output:
    orbits := Set(orbits, Set);

    # Start by getting size of group in each orbit.

    sizes := List(orbits, o -> sizeProjectOrb(G,o));

    #Print(sizes);

    # Now check, for each orbit, if we can prove it is not disjoint to some other orbit.

    mergedorbits := [];

    tryMergeOrbit := function(o)
        local i, mergeo, dosplit, stabo;
        stabo := Stabilizer(G, orbits[o], OnTuples);
        for i in [1..Length(mergedorbits)] do
            for mergeo in mergedorbits[i] do
                #Print([mergeo,o,sizes[mergeo],sizes[o],Size(G), sizeProjectOrb(G, Union(orbits[o],orbits[mergeo])), sizes]);
                if sizeProjectOrb(stabo, orbits[mergeo]) <> sizes[mergeo] then
                #if sizeProjectOrb(G, Union(orbits[o],orbits[mergeo])) <> sizes[o] * sizes[mergeo] then
                    # i and mergo are not disjoint
                    Add(mergedorbits[i], o);
                    return true;
                fi;
            od;
        od;
        return false;
    end;

    # Merge any orbits which are "obviously" not disjoint
    for o in [1..Length(orbits)] do
        if not tryMergeOrbit(o) then
            Add(mergedorbits, [o]);
        fi;
    od;

    # Get current best decomposition (will be an overestimate)
    
    baseorblist := List(mergedorbits, mo -> Union(List(mo, x -> orbits[x])));

    finalorblist := [];

    # split orblist
    doSplit := function(orblist)
        local baseorb, basesize, size, split, unionsplit;
        if Length(orblist) = 1 then
            Add(finalorblist, orblist);
            return;
        fi;
        baseorb := Union(orblist);
        basesize := sizeProjectOrb(G, baseorb);
        # Do in increasing order, also only do sets < |orblist|/2, so we don't do double
        for size in [1..Int(Length(orblist)/2)] do
            for split in IteratorOfCombinations(orblist, size) do
                unionsplit := Union(split);
                if basesize = sizeProjectOrb(G,unionsplit) * sizeProjectOrb(G, Difference(baseorb, unionsplit)) then
                    doSplit(split);
                    doSplit(Difference(orblist, split));
                    return;
                fi;
            od;
        od;
        Add(finalorblist, orblist);
    end;

    doSplit(baseorblist);
    return finalorblist;

end;