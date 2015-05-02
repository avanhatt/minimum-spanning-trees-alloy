open util/integer
open graph

pred complete (g : Graph) {
	all disj x, y : g.vertices |
		some e  : g.edges |
			(e.v1 = x and e.v2 = y) or (e.v2 = x and e.v1 = y)
}

pred directedAcyclic (edges : set Edge, verts : set Vertex) {
	verts = Vertex.(edges.rels)
	all v1, v2: verts |
		let e = v1->v2 |
			e in edges.rels implies
				e not in ^(edges.rels - e)
}

pred undirectedAcyclic (edges : set Edge, verts : set Vertex) {
	verts = Vertex.(edges.rels)
	all v1, v2: verts |
		let e = v1->v2 + v2->v1|
			e in edges.rels implies
				e not in ^(edges.rels - e)
}

pred connected (g : UGraph) {
    all disj v1, v2 : g.vertices |
        v1 in v2.^(neighbors.g)
}

pred edgesConnected (edges: set Edge, verts: set Vertex) {
	verts = Vertex.(edges.rels)
	all disj v1, v2 : verts |
		v1 in v2.^(edges.rels)
}

pred differentGraphs (g1, g2 : Graph) {
	g1.edges != g2.edges
}

run directedAcyclic
