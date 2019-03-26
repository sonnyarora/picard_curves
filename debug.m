debug := 0;

forward debug_print;

debug_print := function(s)
	if debug eq 1 then
		print s;
	end if;

	return 0;
end function;
