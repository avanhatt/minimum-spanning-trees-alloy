open util/integer
open lib/graph
open lib/properties

// Claim: for every complete directed graph (of at least size 3) with a cycle, there is a three-cycle

// Determines whether a graph contains a cycle among some three vertices
pred contains3Cycle (g : Graph) {
    some disj x, y, z : Edge {
        x.v1 = z.v2
        x.v2 = y.v1
        y.v2 = z.v1
    }
}

// Predicate that says there is a complete graph with a cycle that does not contain a three-cycle
assert no3Cycle {
  all g : Graph | {
    (complete[g.edges, g.vertices] and directedAcyclic[g.edges, g.vertices])
    => contains3Cycle[g]
  }
}

// No instance found
check no3Cycle for 7
