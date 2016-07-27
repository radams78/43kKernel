import java.util.*;

public class CoqObject {
    static final String DEFINITION = "Definition ";
    static final String COLON = " : ";
    static final String DEFEQ = " :=\n ";
    static final String PERIOD = ".\n";
    static final String CONS = " :: ";
    static final String NIL = "nil";
    static final String LIST = "list";
    static final String NAT = "nat";

    private String type;
    private String value;

    public CoqObject(String type, String value) {
	this.type = type;
	this.value = value;
    }

    public String getType() { return type; }
    public String getValue() { return value; }
    public String toString() { return "(" + value + ")"; }

    public String definition(String name) {
	return(DEFINITION + name + COLON + type + DEFEQ + value + PERIOD);
    }

    <T extends CoqObject> CoqObject(List<T> list, String type) {
	this.value = "";
	for (T x : list) {
	    assert x.getType().equals(type) : ("Object should have type " + type + " but has type " + x.getType());
	    this.value += x.getValue() + CONS;
	}
	this.value += NIL;
	this.type = LIST + " " + type;
    }

    public static <T extends CoqObject> CoqObject coqList(List<T> list, String type) {
	String value = "";
	for (T x : list) {
	    assert x.getType().equals(type) : ("Object should have type " + type + " but has type " + x.getType());
	    value += x.getValue() + CONS;
	}
	value += NIL;
	return new CoqObject(LIST + " " + type, value);
    }

    public static CoqObject coqInteger(Integer n) {
	assert n >= 0;
	return new CoqObject(NAT, n.toString());
    }

    public static CoqObject coqListInteger(List<Integer> l) {
	ArrayList<CoqObject> integers = new ArrayList<CoqObject>();
	for (Integer n : l) integers.add(coqInteger(n));
	return coqList(integers, NAT);
    }
}
