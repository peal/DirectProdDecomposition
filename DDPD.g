# The function 'DDPD' gives the finest disjoint direct product decomposition of a permutation
# group G, as described in 'Disjoint direct product decompositions of permutation groups'
# by Mun See Chang and Christopher Jefferson.

# This code is licensed under the Mozilla Public License 2.0


LoadPackage("datastructures");

# Given a list of disjoint lists 'l', return a new list 'x'
# such that x[i] = j <-> i in l[j]
listSetToIndicator := function(l)
    local x, i, j;
    x := [];
    for i in [1..Length(l)] do
        for j in l[i] do
            x[j] := i;
        od;
    od;
    return x;
end;

timerec := rec();
DDPD := function(G)
    local orbits, orbitindicator, orbitunion, orbitunionindicator, decomp, orbbase
          ,chain
          ,parts, partsindicator
          ,base, baseorbitchanges, transversals, chainlevels
          ,newtransversals
          , d, o, i, j, t, l, stronggens;
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
    orbitindicator := listSetToIndicator(orbits);
    
    timerec.startStab := NanosecondsSinceEpoch();
    chain := StabChain(G, Concatenation(orbits));
    timerec.endStab := NanosecondsSinceEpoch();
    
    # Gather the base
    base := [chain.orbit[1]];
    # Also gather the permutations used in the transversal
    # of each permutation
    transversals := [Set(chain.transversal)];
    # And store the levels of the stabilizer chain as a list,
    # for fast access later
    chainlevels := [chain];
    # Store the Positions in the base where a new orbit
    # starts.
    # Put '1' in here as a base case
    baseorbitchanges := [1];

    while IsBound(chain.stabilizer) do
        chain := chain.stabilizer;
        if IsBound(chain.orbit) then
            Add(base, chain.orbit[1]);
            l := Length(base);
            if orbitindicator[base[l]] <> orbitindicator[base[l-1]] then
                Add(baseorbitchanges, l);
            fi;
            Add(transversals, Set(chain.transversal));
            Add(chainlevels, chain);
        fi;
    od;

    # Now the main part of the algorithm, we sift the
    # transversal array, using the first base point after the
    # orbit

    newtransversals := [];
    for i in [1..Length(baseorbitchanges)-1] do
        for j in [baseorbitchanges[i]..baseorbitchanges[i+1]-1] do
            newtransversals[j] := [];
            for t in transversals[j] do
                for l in [baseorbitchanges[i+1]..Length(base)] do
                    if base[l]^t <> base[l] then
                        t := SiftedPermutation(chainlevels[l], t);
                    fi;
                od;
                Add(newtransversals[j], t);
            od;
        od;
    od;

    # These parts of the transversals don't get stripped, just copy them over
    Append(newtransversals, transversals{[Last(baseorbitchanges)..Length(transversals)]});


    # Final part. For each orbit, we track which permutations in it's transversal refer to
    # later orbits. Note that they can never refer to earlier orbits. orbitunion[i] is the
    # earliest orbit which is in the same subdirect product part as orbit i.
    orbitunion := PartitionDS(IsPartitionDS, Length(orbits));
    for i in [1..Length(newtransversals)] do
        orbbase := orbitindicator[base[i]];
        for t in MovedPoints(newtransversals[i]) do
            Unite(orbitunion, orbbase, orbitindicator[t]);
        od;
    od;

    parts := Set(PartsOfPartitionDS(orbitunion));
    partsindicator := listSetToIndicator(parts);
    # Needs to be same length as parts
    decomp := List(parts, x -> rec(base := [], genset := []));
    for i in [1..Length(base)] do
        t := partsindicator[orbitindicator[base[i]]];
        Add(decomp[t].base, base[i]);
        Append(decomp[t].genset, newtransversals[i]);
    od;

    for d in decomp do
        d.group := Group(d.genset, ());
        SetStabChainMutable(d.group, StabChainBaseStrongGenerators(d.base, d.genset, ()));
    od;

    return decomp;
    # Store which points in the base 
    #return rec(decomp := decomp, o := PartsOfPartitionDS(orbitunion), c := chainlevels, t := transversals, b := base, newt := newtransversals);
end;


