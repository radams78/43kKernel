import java.util.*;
import java.io.*;

/**
 * A <i>boundary</i> consists of:
 * <ul>
 * <li>a <i>top path</i> as a list of points.
 * <li>a <i>bottom path</i> as a list of points.
 * </ul>
 * Points are represented as integers.  
 *
 * Invariant: The top and bottom paths should have common end-points, called <i>anchors</i>.
 */
public class Boundary extends CoqObject {
    static final String COQTYPE = "Boundary";
    static final String CONSTRUCTOR = "mkBoundary";

    private Path topPath;
    private Path bottomPath;
    /** Number of vertices in both paths, including end-points. */
    public final int size;
    private String name;

    /**
     * Precondition: topPath and bottomPath have the same first and last elements
     */
    public Boundary(Path topPath, Path bottomPath) {
	super(COQTYPE + " " + CoqObject.NAT + " " + topPath.getLength() + " " + bottomPath.getLength(), 
	      CONSTRUCTOR + " " + topPath.getLength() + " " + bottomPath.getLength() + " " + topPath.get(0) + " " + topPath.getLast() + " " + topPath.getMiddle() + " \n " + bottomPath.getMiddle()); // TODO Duplication with other CoqObject constructors?
	assert topPath.get(0).equals(bottomPath.get(0));
	assert topPath.getLast().equals(bottomPath.getLast());
	this.topPath = topPath;
	this.bottomPath = bottomPath;
	this.size = vertexSet().size();
	this.name = name;
    } 

    public Vertex getLeft() { return topPath.get(0); }
    public Vertex getRight() { return topPath.getLast(); }
	
    /** Set of vertices in both paths, including end-points, in order: top path from left to right, then (bottom path - top path) from left to right. */
    public ArrayList<Vertex> vertexSet() {
	ArrayList<Vertex> ans = topPath.asArrayList();
	for(Vertex v : bottomPath.asArrayList()) {
	    if(! ans.contains(v))
		ans.add(v);
	}
	return ans;	
    }
    
    /** Set of all neigbours of a given set of points */
    public Set<Vertex> neighbors(Set<Vertex> S) {
	Set<Vertex> ans = PathOperator.pathNeighbors(topPath, S);	
	ans.addAll(PathOperator.pathNeighbors(bottomPath, S));
	return ans;
    }
    
    /** Tests whether two points are neighbours in the boundary */
    public boolean areNeighbors(Vertex u, Vertex v) {
	Set<Vertex> S = new TreeSet<Vertex> ();
	S.add(u);
	return neighbors(S).contains(v);
    }
    
    public int topPathLength() {return topPath.size() - 2;}
    public int bottomPathLength() {return bottomPath.size() - 2;}
    
    public Vertex leftAnchor() {return topPath.get(0);}
    public Vertex rightAnchor() {return topPath.get(topPath.size() - 1);}
    public Set<Vertex> getAnchors() {
	Set<Vertex> ans = new TreeSet<Vertex> ();
	ans.add(leftAnchor());
	ans.add(rightAnchor());
	return ans;
    }
    
    public Vertex topPathVertex(int p) {return topPath.get(p);}
    public Vertex bottomPathVertex(int p) {return bottomPath.get(p);}
    
    public Path getTopPath(){return new Path(topPath);}
    public Path getBottomPath(){return new Path(bottomPath);}
    
    /** Renumbers the vertices in the order given by {@link #vertexSet} */
    public VertexRenamer canonicalRenamer() {return new VertexRenamer(vertexSet());}
    /** The boundary, as renumbered by {@link #canonicalRenamer} */
    Boundary canonicalBoundary() {return canonicalRenamer().renamedBoundary(this);}
    
    public String toString() {return "<" + topPath.toString() + " - " + bottomPath.toString() + ">";}
    
    public boolean equals(Object o) {
	if(!(o instanceof Boundary)) return false;
	Boundary b = (Boundary) o;
	return topPath.equals(b.getTopPath()) && bottomPath.equals(b.getBottomPath());
	}
    
    /** An input (D, X) is valid if D is disjoint from N(X) */
    public ArrayList<InputPair> allValidInputs() {
	ArrayList<InputPair> ans = new ArrayList<InputPair> ();
	TreeSet<Vertex> allVertices = new TreeSet<Vertex> (vertexSet());
	PowerSet<Vertex> allVertexSubsets = new PowerSet<Vertex>(allVertices);
	for(TreeSet<Vertex> X : allVertexSubsets) {
	    TreeSet<Vertex> possibleD = new TreeSet<Vertex> (allVertices);
	    possibleD.removeAll(neighbors(X));
	    PowerSet<Vertex> allD = new PowerSet<Vertex>(possibleD);
	    for(TreeSet<Vertex> D : allD) {
		ans.add(new InputPair(X,D));
	    }
	}
	return ans;
    }
    
    /** true if b can be glued to the bottom of this */
    public boolean canGlue(Boundary bottomBoundary) {
	
	// FALSE if top and bottom boundaries dont match
	if(bottomPathLength() != bottomBoundary.topPathLength()) return false;
	
	// FALSE if gluing creates a double edge on top and bottom that is not an edge in middle.
	DoubleBoundary DB = preglue(bottomBoundary);
	List<Pair<Vertex, Vertex> > forbiddenEdges = PathOperator.pathEdges(DB.getTopPath());
	forbiddenEdges.retainAll(PathOperator.pathEdges(DB.getBottomPath()));
	forbiddenEdges.removeAll(PathOperator.pathEdges(DB.getMiddlePath()));
	if(!forbiddenEdges.isEmpty()) return false;
	
	return true;	
    }
    
    public DoubleBoundary preglue(Boundary bottomBoundary) {return new DoubleBoundary(this, bottomBoundary);}

    /** glue bottomBoundary onto this and return the resulting outer boundary */
    public Boundary glue(Boundary bottomBoundary) {return preglue(bottomBoundary).getOuterBoundary();}
    
    
    /** Transforms an input pair to Johan Style (i.e (X,S) where S = VertexSet \ (N[X] u D) */
	public InputPair toJohanStyle(InputPair inp) {
	    Set<Vertex> X = new TreeSet<Vertex> (inp.first);
	    Set<Vertex> D = new TreeSet<Vertex> (inp.second);
	    Set<Vertex> NX = neighbors(X);
	    
	    Set<Vertex> S = new TreeSet<Vertex> (vertexSet());
	    S.removeAll(NX);
	    S.removeAll(D);
	    
	    return new InputPair(X,S);
	}
    
    /** Transforms an input pair from Johan Style to Daniel Style
     * (X,S) --> (X, D) where D = VertexSet \ (N[X] u D) 
     * so ironically converting to and from is the same. */
    public InputPair fromJohanStyle(InputPair inp) {return toJohanStyle(inp);}
    
    // TESTING
    public static void main(String[] args) {
	Path topBoundaryTopPath, topBoundaryBottomPath;
	
	Scanner sc = new Scanner(System.in);
	
	System.out.println("Name");
	String name = sc.nextLine();

	System.out.println("Top / Bottom (Path length)");
	int tt, tb;
	tt = sc.nextInt();
	tb = sc.nextInt();
	
	topBoundaryTopPath = new Path();	
	topBoundaryBottomPath = new Path();
	
	while(tt-->0) {topBoundaryTopPath.add(new Vertex(sc.nextInt()));}
	while(tb-->0) {topBoundaryBottomPath.add(new Vertex(sc.nextInt()));}
	
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
