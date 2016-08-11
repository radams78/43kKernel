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
    private final PathLength pathLength;

    public Path(Collection<Vertex> vertices) {
	super(vertices, Vertex.COQTYPE);
	this.vertices = new ArrayList<Vertex>(vertices);
	switch(vertices.size()) {
	case 2: this.pathLength = PathLength.zero; break;
	case 3: this.pathLength = PathLength.one; break;
	case 4: this.pathLength = PathLength.two; break;
	default: throw new IllegalArgumentException("Attempt to create path of length " + vertices.size() + ": " + vertices);
	}
    }

    public Path(Path path) {
	super(path.vertices, Vertex.COQTYPE);
	this.vertices = new ArrayList<Vertex>(path.vertices);
	this.pathLength = path.pathLength;
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

    public PathLength getLength() {
	return pathLength;
    }

    /* Return the points in a path except for the endpoints */
    public CoqObject getMiddle() {
	Vertex[] middle = new Vertex[getLength().toInt];
	for (int i = 0; i < getLength().toInt; i++)
	    middle[i] = get(i + 1);
	return CoqObject.vector(Arrays.asList(middle), Vertex.COQTYPE);
    }
}
