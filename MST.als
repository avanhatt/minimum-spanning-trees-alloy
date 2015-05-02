open util/integer
open lib/graphInheritance
open lib/basicProperties

pred isSpanningTree(g, tree : UGraph) {
	not (g = tree)
    g.vertices = tree.vertices
    tree.edges in g.edges
    undirectedAcyclic[tree]
    connected[tree]
}

pred isInterestingSpanningTree(g, tree : UGraph) {
	g.vertices = Vertex
	smallWeights
	isSpanningTree[g, tree]
	complete[g]
	not undirectedAcyclic[g]
	some e: g.edges | e not in tree.edges
}

fact makingItInteresting {
	all disj g1, g2: Graph |
		g1.edges != g2.edges
	all disj e1, e2: Edge |
		e1.weight != e2.weight
	one g : Graph {
		complete[g] 
	}
	all edgeSubset: set Edge { 
		#edgeSubset = sub[#Vertex, 1] implies
			some graph: UGraph | edgeSubset = graph.edges
		some graph: UGraph | edgeSubset = graph.edges implies
			#edgeSubset = sub[#Vertex, 1] or complete[graph]
	}
}

pred isMST(g, tree : UGraph) {
	isInterestingSpanningTree[g, tree]
		
	no tree2 : UGraph {
        	isSpanningTree[g, tree2]
        	gt[sumOfWeights[tree], sumOfWeights[tree2]]
	}
}

fun sumOfWeights(g : Graph) : Int {
	sum edge : g.edges | edge.weight
}

pred smallWeights {
	all e : Edge |
		e.weight < 10 and e.weight > -10
}

run isMST for exactly 4 Vertex,  21 Graph, 6 Edge, 10 Int
