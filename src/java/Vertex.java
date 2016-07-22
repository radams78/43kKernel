public class Vertex extends CoqObject {
    private final int index;

    public Vertex(int n) {
	super(CoqObject.NAT, String.valueOf(n));
	this.index = n;
    }

    public Vertex plus(int n) {
	return new Vertex(index + n);
    }
}
