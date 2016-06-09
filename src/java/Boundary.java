import java.util.*;

public class Boundary {
	private ArrayList<Integer> topPath;
	private ArrayList<Integer> bottomPath;
	public final int size;
	
	Boundary(ArrayList<Integer> topPath, ArrayList<Integer> bottomPath) {
		this.topPath = new ArrayList<Integer> (topPath);
		this.bottomPath = new ArrayList<Integer> (bottomPath);
		this.size = vertexSet().size();
	} 
	
	public ArrayList<Integer> vertexSet() {
		ArrayList<Integer> ans = new ArrayList<Integer> ();
		ans.addAll(topPath);
		for(int i = 0; i < bottomPath.size(); ++i) {
			if(ans.contains(bottomPath.get(i))) continue;
			ans.add(bottomPath.get(i));
		}
		return ans;	
	}

	public Set<Integer> neighbors(Set<Integer> S) {
		Set<Integer> ans = PathOperator.pathNeighbors(topPath, S);	
		ans.addAll(PathOperator.pathNeighbors(bottomPath, S));
		return ans;
	}
	
	public boolean areNeighbors(int u, int v) {
		Set<Integer> S = new TreeSet<Integer> ();
		S.add(u);
		return neighbors(S).contains(v);
	}
	
	public int topPathLength() {return topPath.size() - 2;}
	public int bottomPathLength() {return bottomPath.size() - 2;}
	
	public int leftAnchor() {return topPath.get(0);}
	public int rightAnchor() {return topPath.get(topPath.size() - 1);}
	public Set<Integer> getAnchors() {
		Set<Integer> ans = new TreeSet<Integer> ();
		ans.add(leftAnchor());
		ans.add(rightAnchor());
		return ans;
	}
	
	public int topPathVertex(int p) {return topPath.get(p);}
	public int bottomPathVertex(int p) {return bottomPath.get(p);}
	
	public ArrayList<Integer> getTopPath(){return new ArrayList<Integer> (topPath);}
	public ArrayList<Integer> getBottomPath(){return new ArrayList<Integer> (bottomPath);}

	public VertexRenamer canonicalRenamer() {return new VertexRenamer(vertexSet());}
	Boundary canonicalBoundary() {return canonicalRenamer().renamedBoundary(this);}
	
	public String toString() {return "<" + topPath.toString() + " - " + bottomPath.toString() + ">";}
	
	public boolean equals(Object o) {
		if(!(o instanceof Boundary)) return false;
		Boundary b = (Boundary) o;
		return topPath.equals(b.getTopPath()) && bottomPath.equals(b.getBottomPath());
	}
	
	// An input is valid if D is disjoint from N(X).
	public ArrayList<InputPair> allValidInputs() {
		ArrayList<InputPair> ans = new ArrayList<InputPair> ();
		TreeSet<Integer> allVertices = new TreeSet<Integer> (vertexSet());
		PowerSet allVertexSubsets = new PowerSet(allVertices);
		for(TreeSet<Integer> X : allVertexSubsets) {
			TreeSet<Integer> possibleD = new TreeSet<Integer> (allVertices);
			possibleD.removeAll(neighbors(X));
			PowerSet allD = new PowerSet(possibleD);
			for(TreeSet<Integer> D : allD) {
				ans.add(new InputPair(X,D));
			}
		}
		return ans;
	}
	
	// true if b can be glued to the bottom of this.
	public boolean canGlue(Boundary bottomBoundary) {
		
		// FALSE if top and bottom boundaries dont match
		if(bottomPathLength() != bottomBoundary.topPathLength()) return false;
		
		// FALSE if gluing creates a double edge on top and bottom that is not an edge in middle.
		DoubleBoundary DB = new DoubleBoundary(this, bottomBoundary); 
		List<Pair<Integer, Integer> > forbiddenEdges = PathOperator.pathEdges(DB.getTopPath());
		forbiddenEdges.retainAll(PathOperator.pathEdges(DB.getBottomPath()));
		forbiddenEdges.removeAll(PathOperator.pathEdges(DB.getMiddlePath()));
		if(!forbiddenEdges.isEmpty()) return false;
		
		return true;	
	}
	
	// glue b onto this and return the resulting outer boundary
	public Boundary glue(Boundary bottomBoundary) {return (new DoubleBoundary (this, bottomBoundary)).getOuterBoundary();}

	
	// Transforms an input pair to Johan Style (i.e (X,S) where S = VertexSet \ (N[X] u D)
	public InputPair toJohanStyle(InputPair inp) {
		Set<Integer> X = new TreeSet<Integer> (inp.first);
		Set<Integer> D = new TreeSet<Integer> (inp.second);
		Set<Integer> NX = neighbors(X);
	
		Set<Integer> S = new TreeSet<Integer> (vertexSet());
		S.removeAll(NX);
		S.removeAll(D);
		
		return new InputPair(X,S);
	}
	
	// Transforms an input pair from Johan Style to Daniel Style
	// (X,S) --> (X, D) where D = VertexSet \ (N[X] u D) 
	// so ironically converting to and from is the same.
	public InputPair fromJohanStyle(InputPair inp) {return toJohanStyle(inp);}
	
	
	// TESTING
	public static void main(String[] args) {
		ArrayList<Integer> topBoundaryTopPath, topBoundaryBottomPath;
			
		Scanner sc = new Scanner(System.in);
			
		System.out.println("Top / Bottom (Path length)");
		int tt, tb;
		tt = sc.nextInt();
		tb = sc.nextInt();
			
		topBoundaryTopPath = new ArrayList<Integer>();	
		topBoundaryBottomPath = new ArrayList<Integer>();

		while(tt-->0) {topBoundaryTopPath.add(sc.nextInt());}
		while(tb-->0) {topBoundaryBottomPath.add(sc.nextInt());}
				
		Boundary topB = new Boundary(topBoundaryTopPath, topBoundaryBottomPath);
			
		System.out.println("Resulting Boundary: ");
		System.out.println(topB);
			
		System.out.println("Canonical Form Boundary: ");
		System.out.println(topB.canonicalBoundary());
			
		System.out.println("All valid inputs");
		for(InputPair P : topB.allValidInputs()) {System.out.println(P);}
		
		sc.close();
	}
	
	
}