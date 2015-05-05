open util/integer
open util/natural
open util/ordering[State]
open lib/graph
open MST
open lib/properties

sig State {
	// The graph we're operating on
	g : one UGraph,

	// Clouds
	parentSet : Vertex -> Vertex,

	// Ranks
	ranks : Vertex -> Natural,

	// Edges we haven't tried to add yet
	remainingEdges : set Edge,

	// The edges that we've already added to our MST
	edgesInMST : set Edge
}{
	some g.edges
}

fun minEdges(es : set Edge) : Edge {
	// This returns the set of the edges of the smallest weight if there are multiple
	{e : es | no e2 : es | lt[e2.weight, e.weight]}
}

fact initialState {
	// Otherwise this will return a spanning forest instead of a spanning tree
	connected[first.g.edges, first.g.vertices]

	// All parent pointers start off pointing to themselves
	all v1, v2 : Vertex |
		v1 -> v2 in first.parentSet iff (v1 = v2) and (v1 in first.g.vertices)

	// Initial ranks are 0
	first.ranks = Vertex -> Zero

	first.remainingEdges = first.g.edges
	no first.edgesInMST
}

fact endState {
	no last.remainingEdges
}

abstract sig Event {
	pre, post : State
}

sig addEdge extends Event { }
{
	// These all must be operating on the same graph!
	post.g = pre.g

	// Go in order of edge weight
	let minEs = minEdges[pre.remainingEdges] |
		some minE : minEs |
		some p1, p2: Vertex {
			post.remainingEdges = pre.remainingEdges - minE
			findAndCompress[minE.v1, p1, pre, post]
			findAndCompress[minE.v2, p2, pre, post]
			// This edge can be added to the MST
			(p1 != p2) => {
				// Add it to the MST and update the parent pointers
				post.edgesInMST = pre.edgesInMST + minE

				// If their ranks are equal, arbitrarily choose that p1 points to p2
				p1.(pre.ranks) = p2.(pre.ranks) =>{
					// If p1 has a smaller rank, make p1 point to p2
					updateRoots[minE.v1, minE.v2, p1, p2, pre, post]
					//increment the rank of the new parent
					let curRank = p2.(pre.ranks) | 
						post.ranks = pre.ranks - (p2 -> curRank) + (p2 -> inc[curRank])

				} else { lt[p1.(pre.ranks), p2.(pre.ranks)] => {
					// If p2 has a smaller rank, make p1 point to p2
					updateRoots[minE.v1, minE.v2, p1, p2, pre, post]
					post.ranks = pre.ranks
				
				} else {
					// If p1 has a smaller rank, make p2 point to p1
					updateRoots[minE.v2, minE.v1, p2, p1, pre, post]
					post.ranks = pre.ranks			
				}}
			} else {
				// The clouds/MST are still the same
				post.edgesInMST = pre.edgesInMST
				updateParents[minE.v1, minE.v2, p1, p2, pre, post]
				post.ranks = pre.ranks
			}
		}
}

// Everything stays the same, except path compression
pred updateParents(v1, v2, p1, p2 : Vertex, pre, post : State) {
	let trans1 = v1.^(pre.parentSet) | let trans2 =  v2.^(pre.parentSet) | //trans1 and trans2 are the vertices in each cloud
		let others = Vertex - (trans1 + trans2 + p1 + p2) | //everything that's not in either cloud
			let otherRels = (others -> Vertex) & pre.parentSet | 
				//the parentSet has everything from the first cloud pointing to p1, everything from the second
				//cloud pointing to p2, everything from neither cloud the same as it was, and p1 pointing to p2
				post.parentSet = (trans1 -> p1) + (trans2 -> p2) + otherRels
}

// Merge two clouds by choosing v2 to be the new root, allow path compression
pred updateRoots(v1, v2, p1, p2 : Vertex, pre, post : State) {
	v1 -> v2 in post.parentSet
	let trans1 = v1.^(pre.parentSet) | let trans2 =  v2.^(pre.parentSet) | //trans1 and trans2 are the vertices in each cloud
		let others = Vertex - (trans1 + trans2 + p1 + p2) | 
			let otherRels = (others -> Vertex) & pre.parentSet | //everything that's not in either cloud
				//the parentSet has everything from the first cloud pointing to p1, everything from the second
				//cloud pointing to p2, everything from neither cloud the same as it was, and p1 pointing to p2
				post.parentSet = ((trans1 - p1) -> p1) + (trans2 -> p2) + (p1 -> p2) + otherRels
}

pred findAndCompress(v, p : Vertex, pre, post : State) {
	// p is the root of v's cloud if it's in the transitive closure of v in the parentSet and it's related to itself in the parentSet
	p in v.^(pre.parentSet) 
	p -> p in pre.parentSet
	
	// to compress the tree, all vertices in the transitive closure of v in the parentSet now point directly to p
	all disj v1, v2 : (v.^(pre.parentSet) + v) |
		v1 -> v2 in post.parentSet iff v2 = p
}

fact transitions {
	all s: State - last |
		let s' = s.next |
			one e: Event | e.pre = s and e.post = s'
}

//assertion that a sequence of addEdge events will always result in an MST of the graph
assert findsMST {
	isMST[last.edgesInMST, last.g]
}

// for n Vertex -> 10 Int, (n-1) Natural, exactly (n choose 2) Edge, 1 Graph
//	  		     n Vertex,  (n choose 2)+1 State, (n choose 2) Event

//check findsMST for 10 Int, 3 Natural, exactly 3 Edge, 1 Graph, 3 Vertex, 4 State, 3 Event
check findsMST for 10 Int, 3 Natural, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event

// run { } for 10 Int, 2 Natural, exactly 3 Edge, 1 Graph, 3 Vertex, 4 State, 3 Event
//run { } for 10 Int, 5 Natural, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event
run { } for 10 Int, 9 Natural, exactly 10 Edge, 1 Graph, 5 Vertex, 11 State, 10 Event
