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
    @Override public String toString() { return "(" + value + ")"; }

    public String definition(String name) {
	return(DEFINITION + name + COLON + type + DEFEQ + value + PERIOD);
    }

    //TODO Magic strings
    <T extends CoqObject> CoqObject(Iterable<T> list, String type) {
	String prefix = "", suffix = "";
	for (T x : list) {
	    assert x.getType().equals(type) : ("Object should have type " + type + " but has type " + x.getType());
	    prefix = "List.cons (" + x.getValue() + ") (" + prefix;
	    suffix += ")";
	}
	this.value = prefix + "List.nil" + suffix;
	this.type = LIST + " " + type;
    }

    public static <T extends CoqObject> CoqObject vector(List<T> list, String type) {
	String value = "";
	for (T x : list) {
	    assert x.getType().equals(type) : ("Object should have type " + type + " but has type " + x.getType());
	    value += x.getValue() + CONS;
	}
	value += "(" + NIL + " " + type + ")";
	return new CoqObject("t " + type, value);
    }

    public static String construct(String constructor, List<CoqObject> arguments) {
	String result = constructor;
	for (CoqObject arg : arguments)
	    result += " " + arg;
	return result;
    }
}
