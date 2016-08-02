import java.util.*;

public class Path extends CoqObject {
    enum PathLength {
	zero(0), one(1), two(2);

	public final int toInt;

	PathLength(int toInt) {
	    this.toInt = toInt;
	}
    }

    private ArrayList<Vertex> vertices;

    public Path() {
	super(new ArrayList<Vertex>(), Vertex.COQTYPE);
	this.vertices = new ArrayList<Vertex>();
    }

    public Path(List<Vertex> vertices) {
	super(vertices, Vertex.COQTYPE);
	this.vertices = new ArrayList<Vertex>();
	this.vertices.addAll(vertices);
    }

    public Path(Path path) {
	super(path.vertices, Vertex.COQTYPE);
	this.vertices = new ArrayList<Vertex>(path.vertices);
    }

    public Vertex get(int i) {
	return vertices.get(i);
    }

    public Vertex getLast() {
	return vertices.get(size() - 1);
    }

    public ArrayList<Vertex> asArrayList() {
	return new ArrayList<Vertex>(vertices);
    }

    public int size() {
	return vertices.size();
    }

    public void add(Vertex v) {
	vertices.add(v);
    }

    public PathLength getLength() {
	return PathLength.zero;
    }

    /* Return the points in a path except for the endpoints */
    public CoqObject getMiddle() {
	Vertex[] middle = new Vertex[getLength().toInt];
	for (int i = 0; i < getLength().toInt; i++)
	    middle[i] = get(i + 1);
	return CoqObject.vector(Arrays.asList(middle), Vertex.COQTYPE);
    }
}
