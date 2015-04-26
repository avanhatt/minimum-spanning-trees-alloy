open util/integer
open lib/graph
open lib/basicproperties

pred contains3Cycle (g : Graph) {
    some disj x, y, z : Edge {
        x.v1 = z.v2
        x.v2 = y.v1
        y.v2 = z.v1
    }
}

pred no3Cycle (g : Graph) {
    complete[g]
    not directedAcyclic[g]
    not contains3Cycle[g]
}

run no3Cycle for 7
