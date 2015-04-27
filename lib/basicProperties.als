open util/integer
open graph

pred noSelfEdges (g : Graph){
    no edge: g.edges |
        edge.v1 = edge.v2
}

pred oneWayNoDuplicateEdges (g: Graph) {
    all disj edge1, edge2 : g.edges |  { 
            let verts1 = edge1.v1 + edge1.v2 |
            let verts2 = edge2.v1 + edge2.v2 |
            verts1 != verts2
            }
}

pred twoWayNoDuplicateEdges (g: Graph) {
    all disj edge1, edge2 : g.edges |
        edge1.v1 = edge2.v1 implies edge1.v2 != edge2.v2
}

pred undirectedAcyclic (g : Graph) {
    all v1, v2 : Vertex |
        let e = v1->v2 + v2->v1 |
            e in neighbors implies
                e not in ^(neighbors - e)
}

pred complete (g : Graph) {
    all disj x, y : g.vertices |
        some e  : g.edges |
            (e.v1 = x and e.v2 = y) or (e.v2 = x and e.v1 = y)
}

pred directedAcyclic (g : Graph) {
    all v : Vertex |
        v->v not in ^(successors)
}

pred connected (g : Graph) {
    all disj v1, v2 : g.vertices |
        v1 in v2.^neighbors
}

fact isValidGraph{
    all g : Graph {
        noSelfEdges[g]
        oneWayNoDuplicateEdges[g]
        hasCorrectEdgesVertices[g]
    }
}
