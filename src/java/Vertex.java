public class Vertex extends CoqObject implements Comparable<Vertex> {
    private final int index;

    public Vertex(int n) {
	super(CoqObject.NAT, String.valueOf(n));
	this.index = n;
    }

    public Vertex plus(int n) {
	return new Vertex(index + n);
    }

    public int compareTo(Vertex n) {
	return new Integer(index).compareTo(new Integer(n.index));

    }
}
