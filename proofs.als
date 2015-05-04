open util/integer
open lib/graph
open lib/basicProperties

//claim: for every complete directed graph (of at least size 3) with a cycle, there is a three-cycle

//determines whether a graph contains a cycle among some three vertices
pred contains3Cycle (g : Graph) {
    some disj x, y, z : Edge {
        x.v1 = z.v2
        x.v2 = y.v1
        y.v2 = z.v1
    }
}

//predicate that says there is a complete graph with a cycle that does not contain a three-cycle
pred no3Cycle (g : Graph) {
    complete[g]
    not directedAcyclic[g]
    not contains3Cycle[g]
}
//no instance found
run no3Cycle for 7
