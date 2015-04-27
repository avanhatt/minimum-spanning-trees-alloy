open util/integer

sig Vertex {
    neighbors : set Vertex -> Graph,
    successors : set Vertex
}

sig Edge { 
    v1: one Vertex,
    v2: one Vertex,
    weight: Int
}

sig Graph {
    edges: set Edge,
    vertices: set Vertex
}

fact neighbors {
    all graph : Graph | {
        all vertex : graph.vertices {
            all edge : graph.edges {
                vertex = edge.v1 implies edge.v2 in vertex.neighbors.graph
                vertex = edge.v2 implies edge.v1 in vertex.neighbors.graph
			}
        	all neighbor : vertex.neighbors.graph |
            	some edge : graph.edges {
                	edge.v1 = vertex and edge.v2 = neighbor or
                	edge.v2 = vertex and edge.v1 = neighbor
            	}
			}
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

fact graphMembership {
    all edge: Edge |
        some g : Graph {
            edge in g.edges}
    all vertex: Vertex |
        some g : Graph {
            vertex in g.vertices}
            
}

run {}
