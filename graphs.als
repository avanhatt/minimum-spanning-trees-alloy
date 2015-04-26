open util/integer

sig Vertex {
    neighbors : set Vertex,
    successors : set Vertex
}

sig Edge { 
    v1: one Vertex,
    v2: one Vertex,
    weight: Int
}

one sig Graph {
    edges: set Edge,
    vertices: set Vertex
}

fact neighbors {
    all vertex : Vertex |
        all edge : Edge {
            vertex = edge.v1 implies edge.v2 in vertex.neighbors
            vertex = edge.v2 implies edge.v1 in vertex.neighbors
        }
    all vertex : Vertex |
        all neighbor : vertex.neighbors |
            some edge : Edge {
                edge.v1 = vertex and edge.v2 = neighbor or
                edge.v2 = vertex and edge.v1 = neighbor
            }
}

fact successors { 
    all vertex : Vertex {
        all edge : Edge |
            vertex = edge.v1 implies edge.v2 in vertex.successors
        all successor : vertex.successors |
            some edge : Edge |
                edge.v1 = vertex and edge.v2 = successor
    }
}

pred hasCorrectEdgesVertices (g : Graph) {
    all edge : g.edges |
        edge.v1 in g.vertices and
        edge.v2 in g.vertices
    all vertex : g.vertices |
        all edge : Edge {
            edge.v1 = vertex implies edge in g.edges
            edge.v2 = vertex implies edge in g.edges
        }
}

pred noSelfEdges (g : Graph){
    no edge: g.edges |
        edge.v1 = edge.v2
}

fact graphMembership {
    all edge: Edge |
        some g : Graph {
            edge in g.edges}
    all vertex: Vertex |
        some g : Graph {
            vertex in g.vertices}
            
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

fact isValidGraph{
    all g : Graph {
        noSelfEdges[g]
        oneWayNoDuplicateEdges[g]
         hasCorrectEdgesVertices[g]
    }
}

run no3Cycle for 7
