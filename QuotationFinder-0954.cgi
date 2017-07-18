#!/usr/bin/perl  -w
																				# Tells Unix where to find the Perl interpreter; Camel3 1.3.1. 
																				# If Perl is installed somewhere else on your system, you will 
																				# have to change this line accordingly.
# ACHTUNG: Wenn Programm fertig: "-w" löschen! Effektiv 167
# ACHTUNG: DAS PROGRAMM SETZT VORAUS, DASS COOKIES AKZEPTIERT WERDEN (MELTZER/MICHALSKI 14.3 (374)). KANN MAN EINE INTELLIGENTE WARNUNG EINBAUEN?
# ODER MÜSSEN ALLE BENUTZER AUF DER TITELSEITE DARAUF AUFMERKSAM GEMACHT WERDEN?
# SIEHE CGI 290 "TESTING FOR COOKIES"!

### QuotationFinder

# Version History:
# 095:
# Improved sorting of word form lists and removal of near-identical matches.
# 094:
# Improved Greek Unicode input compatibility.
# 093:
# Introduced JavaScript form validation (error message popups) and handling of TLG Workplace error messages.
# 092:
# Improved handling of CLCLT's Latin u/v non-distinction and compatibility of 'Get back' links.
# 091:
# Improved matching of hyphenated words and removal of near-identical matches.
# 09:
# Increased speed by skipping previously searched texts; added filter to avoid near-identical matches in search results.
# 083:
# Improved color highlighting to distinguish between quotation core and other matched words.
# 082:
# Added verification of upload file format and indication of search progress in percent.
# 081:
# Made Search Progress page more compatible.
# 08:
# Changed base for quotation center calculation (position instead of density of matched words).
# 078:
# Improved quotation center calculation.
# 077:
# Added compatibility with version 5 of CLCLT.
# 076:
# Improved word frequency calculation.
# 075:
# Improved density points calculation.
# 074:
# Improved position points calculation.
# 073:
# Improved occurrence points calculation.
# 072:
# Improved density points calculation.
# 071:
# Established a limit of 100 quotations/allusions for performance and stability reasons.
# 07:
# Added support for TLG Workplace.
# 0651:
# Improved handling of search deletions.
# 065:
# Added Search Progress page.
# 064:
# Improved the occurrence points calculation.
# 063:
# Improved the density points calculation.
# 0622:
# Turned some of the Beta Code formatting into HTML/CSS.
# 0621:
# Worked on HTML to make layout more consistent across browsers and platforms.
# 062:
# Added option of matching parts of words (eliminating the need to enter all forms).
# 061:
# Added 'Easy mode'.
# 06:
# Added support for Greek and for TLG searches.
# 0564:
# Added the option of keeping or deleting old search results when searching new text files.
# 0563:
# Introduced a default value for GenFreq, changed the way HTML creates blank lines, extended the help function.
# 0562:
# Added help function.
# 0561:
# Added the option of deleting old searches; bug fixes.
# 056:
# Added file uploading, multi-user capabilities, and option of starting new searches while keeping old ones stored.
# 0557:
# Added more comments, standardized name to QuotationFinder, added security features, separated configuration from primary code.
# 0556:
# Changed CSS path; tweaked HTML for Windows browsers.
# 0555:
# Improved points position calculation.
# 0554:
# Improved toolbar and form/cognate column display.
# 0553:
# Made calculations of center of matches more efficient.
# 552:
# Enabled CSS, prevented caching.
# 0551:
# Fixed pointsTotal calculation.
# 055:
# Position calculations based on center of matches, not average of match positions.

$| = 1;																	# Keeps Perl from buffering output; CGI Programming 3.3 (59), 15.2 
																		# (366), Cookbook 7.12. This is important because users should get 
																		# some kind of visual feedback soon after a search has started. 
																		# Unbuffering Perl in this way slows scripts down according to CGI 101
																		# 20.3 (186), but I have not seen any difference at all: A test run 
																		# with this CGI took  2.5 minutes both with and without buffering.

# THE FIRST PART OF THE PROGRAM WAS ORIGINALLY INSPIRED BY A PROGRAM BY BRENT MICHALSKI, AVAILABLE AT 
# http://www.webreview.com/1998/10_09/developers/10_09_98_2.shtml

use CGI qw(:standard escapeHTML -unique_headers);						# Loads the CGI.pm module into the program; Cookbook 19.1, CGI.pm 2.9 
																		# (87), 2.1 (24), CGI 5.5 (117). The :standard argument imports the 
																		# standard functions into the script. escapeHTML replaces user input
																		# characters that would be special characters in HTML with their HTML 
																		# entities. -unique_headers makes sure we never get more than 1 HTML 
																		# header (this would crash the program.) These functions are part of
																		# the CGI.pm module.
use CGI::Carp qw(fatalsToBrowser);										# Loads the Carp package; Cookbook 19.2. Carp is part of the standard
																		# CGI.pm distribution and it allows us to get more graceful error mes-
																		# sages. By using Carp fatalsToBrowser, we get most of the error messa-
																		# ges on the browser rather than getting the nasty "500 Internal Server
																		# Error."
use strict;																# Makes sure I don't forget to declare variables; Learning 8.7, Camel3
																		# 4.9.2.
use Data::Dumper;														# Makes it easy to create readable output from hashes and allows for
																		# saving of hashes to files; Advanced 10.2.2, Cookbook 11.11.
use locale;																# Tells Perl's case-conversion functions and pattern matching engine to 
																		# respect your language environment, allowing for characters with dia-
																		# critical marks, and so on; Cookbook 1.9, 6.12.
use DB_File;															# Allows saving of hashes to disk; DBI 2.7 (32), CGI Programming 10.2
																		# (239f).
use MLDBM qw( DB_File Data::Dumper );									# Allows saving of complex data structures to disk; Cookbook 11.14,
																		# 14.8, DBI 2.9 (51), CGI Programming 10.2 (242).
																		# ONCE EVERYTHING WORKS WELL, I SHOULD MAYBE USE STORABLE INSTEAD OF
																		# DATA::DUMPER FOR SPEED REASONS; COOKBOOK 14.9.
																		# ALSO: MLDBM SEARCHES ARE ONLY POSSIBLE VIA HASH KEY. IF MORE FLEXIBLE
																		# SEARCH OPTIONS ARE NEEDED, I'M GOING TO HAVE TO MOVE TO DBI AND A 
																		# SQL DATABASE; COOKBOOK 14.0.
use Fcntl;																# Defines O_RDWR, O_CREAT, etc. under Unix; CGI 10.2 (241), DBI 2.9 
																		# (51), Schilli 1.13.
#use File::Basename;														# Allows us to easily extract a filename from a string that contains a
#LÖST FEHLERMELDUNG AUS (TERMINAL)																		# full pathname; Cookbook 9.10.
use File::Path;															# Allows us to easily remove a directory with all directories and files
																		# it may contain; Cookbook 9.8.
#use utf8;																# Camel3 5.3.3.


BEGIN {																	# Ensures the variables get initialized before the following subroutine
																		# is ever called; Camel3 6.2.3.
	sub carp_error {													# Begins the carp_error subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine displays error messages to the user.
		my $errorMessage = shift;										# Removes an element from the @_ array (containing the values passed to
																		# the subroutine) and stores it in the errorMessage variable; Camel3 
																		# 29.2.149, CGI 5.5 (116).
		my $q = new CGI;												# Prints the error message to the user's browser window, using CGI.pm
			$q->start_html ( "Error" ),									# in object oriented mode; CGI.pm 3.6 (130).
			$q->h1( "Error" ),
			$q->p( "Sorry, the following error has occurred: " );		# KANN DAS ÜBERHAUPT FUNKTIONIEREN? ES GIBT JA KEINE errorMessge ZU
			$q->p( $q->i( $errorMessage ) ),							# shiftEN! IST DIES NICHT NUR FÜR MODULE GEEIGNET?
			$q->end_html;
	}																	# Closes the error subroutine; Camel3 6.2, Cookbook 10.0.
	CGI::Carp::set_message( \&carp_error );								# Passes CGI::Carp::set_message a reference to the carp_error subrou-
																		# tine above; CGI 5.5 (116).
}																		# Closes the BEGIN block; Nutshell 4.3.


my ($message, $note, $caption, $buttonText, $name, $refTextName);									# Declares private variables to exist only within the file; Camel3 
my ($searchCount, $textCount, $wordCount, $work, $key, $field, $x);											# 2.5., 4, 29.2.99, Cookbook 10.2.
my (@textResults, @wordResults, @fileNames, @descriptions, @enMt);
my (%userPasses, %refTextNames, %refText, %textFiles);
my $fileFormat;
my $chunk;
my $scoreSize;


# The following will allow us to split Beta Code strings into multiple-byte chunks; Cookbook 6.18.
my $beta = q{
		\*[\(\)/ß=\+\|]*[A-Z]
	|	S[1-3]
	|	[A-Z][\(\)/ß=\+\|]*
	|	\$\d?\d?
	|	&\d?\d?
	|	@\d?\d?
	|	[\{\}]\d?\d?
	|	[<>]\d?\d?\d?
	|	(\s)?"\d?\d?
	|	[\[\]]\d?\d?
	|	%\d?\d?\d?
	|	\*?#\d?\d?\d?\d?
	|	[\?\.,:;'\-_]
	|	\s
};																		# There are problems splitting strings on multiple-byte characters that contain backslashes. This is why we will
																		# be replacing every backslash with a German sharp s below. Accordingly,
																		# we need to have sharp s here instead of backslash as well.

# The following will allow us to split SymbolGreek strings into individual multiple-byte SymbolGreek characters; Cookbook 6.18.
	
my $sygr = q{
		j[A-ZÁ]/?
	|	[a-z][/ß\[\]\{\}\|;v'`jJ÷\?¿ü>]*
	|	[/ß\[\]\{\}\|J‘’“”«»∆Æ]*[A-ZÁ][/ü]?
	|	&\w*;
	|	["~:…·‚\*¢›∞ﬁ\^&£‹¡™€‡¶•Ö⁄óªº\.Æ∆'`É…<][\dÌﬂ]?
	|	\s
};

# The following will allow us to split SGkClassic strings into individual multiple-byte SymbolGreek characters; Cookbook 6.18.
	
my $sgk = q{
		ÅÅÇ
	|	[+ƒ‰‘·—¡√”„‡¿–Â’≈‚¬)π©(∏®]?[A-Z]
	|	[a-z#%ºª∫]ßß\+?
	|	[a-z#%ºª∫][ƒ‰‘·—¡√”„‡¿–Â’≈“‚¬‹Ï/øØ=ΩÕ)π©(∏®]?\+?
	|	[÷◊ÿ]\d?\d?\d?
	|	["]\d?\d?
	|	[<>]2?
	|	[\[\]ûüàâ]
	|	[ùÇÉÅÑÖÅÜåôã»é¢ﬁﬂæ]
	|	ß[{}]?
	|	[{}]
	|	[úß±≤µ≥]
	|	[:;.,'\-Æ›?!+ „Ÿ⁄/]
	|	\d
};


my %punctuation = (															# Beta Code punctuation; cf. quickbeta.pdf from http://www.tlg.uci.edu/BetaCode.html
	"\?"		=>	"&#x0323;",
	"\."		=>	"\.",
	","		=>	",",
	":"		=>	"&#x0387;",
	";"		=>	"&#x037E;",
	"'"		=>	"&#x2019;",
	"-"		=>	"-",
	"_"		=>	"&#x2014;",
);

my %fontChanges = (															# Beta Code font changes; cf. quickbeta.pdf from http://www.tlg.uci.edu/BetaCode.html
	"\$"	=>	"\$",															# Greek      </span><span style='font-family: $greekFont'>
	"\$1"	=>	"\$1",															# Greek bold </span><span style='font-family: $greekFont,'>
	"&"	=>	"&",															# Greek      </span><span style='font-family: $greekFont'>
);

my %pageFormatting = (															# Beta Code page formatting; cf. quickbeta.pdf from http://www.tlg.uci.edu/BetaCode.html
	"@"		=>	"<spacer>",
	"\@1"	=>	"",															# Page End
	"\@6"	=>	"<br>",														# Blank Line
	"\@8"	=>	"<spacer>",													# Mid-Line Citation
);

my %markup = (
	"{1"	=>	"<span style='font-size: larger'>",
	"}1"	=>	"</span>",
);

my %textFormatting = (
	"<2"	=>	"&#x2032;",
	">2"	=>	"&#x2035;",
	"<20"	=>	"",
	">20"	=>	"",
);

my %quotationMarks = (
	' "'	=>	" &#x0022;",
	'"'		=>	"&#x0022;",
	' "1'	=>	" &#x201E;",
	'"1'	=>	"&#x201E;",
	' "2'	=>	" &#x201C;",
	'"2'	=>	"&#x201C;",
	' "3'	=>	" &#x2018;",
	'"3'	=>	"&#x2019;",
	' "4'	=>	" &#x201A;",
	'"4'	=>	"&#x201A;",
	' "5'	=>	" &#x201B;",
	'"5'	=>	"&#x201B;",
	' "6'	=>	" &#x00AB;",
	'"6'	=>	"&#x00BB;",
	' "7'	=>	" &#x2039;",
	'"7'	=>	"&#x203A;",
	' "8'	=>	" &#x201C;",
	'"8'	=>	"&#x201E;",
);

my %parentheses = (
	"["		=>	"&#x005B;",
	"]"		=>	"&#x005D;",
	"[1"	=>	"&#x0028;",
	"]1"	=>	"&#x0029;",
	"[2"	=>	"&#x2329;",
	"]2"	=>	"&#x232A;",
	"[3"	=>	"&#x007B;",
	"]3"	=>	"&#x007C;",
	"[4"	=>	"&#x301A;",
	"]4"	=>	"&#x301B;",
);

my %addPunctuation = (														# Beta Code additional punctuation and characters; cf. quickbeta.pdf from http://www.tlg.uci.edu/BetaCode.html
	"%"		=>	"&#x2020;",
	"%1"	=>	"&#x003F;",
	"%2"	=>	"&#x002A;",
	"%3"	=>	"&#x002F;",
	"%4"	=>	"&#x0021;",
	"%5"	=>	"&#x007C;",
	"%6"	=>	"&#x003D;",
	"%7"	=>	"&#x002B;",
	"%8"	=>	"&#x0025;",
	"%9"	=>	"&#x0026;",
	"%10"	=>	"&#x003A;",
	"%11"	=>	"&#x00B7;",
	"%12"	=>	"&#x002A;",
	"%13"	=>	"&#x2021;",
	"%14"	=>	"&#x00A7;",
	"%15"	=>	"&#x02C8;",
	"%16"	=>	"&#x00A6;",
	"%17"	=>	"&#x2016;",
	"%18"	=>	"&#x0027;",
	"%19"	=>	"&#x002D;",
	"%20"	=>	"&#x0301;",
	"%21"	=>	"&#x0300;",
	"%22"	=>	"&#x0302;",
	"%23"	=>	"&#x0308;",
	"%24"	=>	"&#x0303;",
	"%25"	=>	"&#x0327;",
	"%26"	=>	"&#x0304;",
	"%27"	=>	"&#x0306;",
	"%28"	=>	"&#x0308;",
	"%30"	=>	"&#x1FBD;",
	"%31"	=>	"&#x1FBF;",
	"%32"	=>	"&#x1FFD;",
	"%33"	=>	"&#x1FEF;",
	"%34"	=>	"&#x1FC0;",
	"%35"	=>	"&#x1FCE;",
	"%36"	=>	"&#x1FDE;",
	"%37"	=>	"&#x1FDD;",
	"%38"	=>	"&#x1FDF;",
	"%39"	=>	"&#x00A8;",
	"%40"	=>	"&#x2692;",
	"%41"	=>	"&#x2013;",
	"%42"	=>	"&#x2696;",
	"%43"	=>	"&#x00D7;",
	"%44"	=>	"&#x2693;",
	"%45"	=>	"&#x2694;",
	"%46"	=>	"&#x2595;",
	"%93"	=>	"&#x0359;",
	"%94"	=>	"&#x0307;",
	"%95"	=>	"&#x0358;",
	"%96"	=>	"&#x035C;",
	"%97"	=>	"&#x0308;",
	"%98"	=>	"&#x0022;",
	"%100"	=>	"&#x003B;",
	"%101"	=>	"&#x0023;",
	"%102"	=>	"&#x2018;",
	"%103"	=>	"&#x005C;",
	"%104"	=>	"&#x005E;",
	"%105"	=>	"&#x007C;&#x007C;&#x007C;",
	"%106"	=>	"&#x224C;",
	"%107"	=>	"&#x007E;",
	"%108"	=>	"&#x00B1;",
	"%109"	=>	"&#x00B7;",
	"%110"	=>	"&#x25CB;",
	"%127"	=>	"&#x032F;",
	"%128"	=>	"&#x030C;",
	"%129"	=>	"&#x2020;",
	"%130"	=>	"&#x0307;",
	"%132"	=>	"&#x1FEE;",
	"%133"	=>	"&#x1FCD;",
	"%134"	=>	"&#x1FCF;",
	"%141"	=>	"&#x2697;",
	"%142"	=>	"&#x2510;",
	"%144"	=>	"&#x2697;&#x0336;",
	"%145"	=>	"&#x2013;&#x0301;",
	"%146"	=>	"&#x00B7;",
	"%147"	=>	"&#x030A;",
	"%148"	=>	"&#x030C;",
	"%149"	=>	"&#x0328;",
	"%150"	=>	"&#x007C;",
	"%154"	=>	"&#x2234;",
	"%155"	=>	"&#x2235;",
	"%158"	=>	"&#x2042;",
	"%159"	=>	"&#x00D7;",
	"%160"	=>	"&#x002D;",
	"%161"	=>	"&#x00F7;",
	"%162"	=>	"&#x0338;",
	"%163"	=>	"&#x00B6;",
	"%171"	=>	"&#x002F;&#x002F;",
	"%172"	=>	"&#x1FBD;",
	"%173"	=>	"&#x1FFE;",
	"%174"	=>	"&#x1FFD;",
	"%175"	=>	"&#x1FEF;",
	"%176"	=>	"&#x1FC0;",
	"%177"	=>	"&#x0313;",
	"%178"	=>	"&#x0314;",
);

my %addCharacters = (															# Beta Code additional characters; cf. quickbeta.pdf from http://www.tlg.uci.edu/BetaCode.html
	"#"		=>	"&#x0374;",
	"*#1"	=>	"&#x03DE;",
	"#1"	=>	"&#x03DF;",
	"*#2"	=>	"&#x03DA;",
	"#2"	=>	"&#x03DB;",
	"*#3"	=>	"&#x03D8;",
	"#3"	=>	"&#x03D9;",
	"*#5"	=>	"&#x03E0;",
	"#5"	=>	"&#x03E1;",
	"#9"	=>	"&#x0301;",
	"#12"	=>	"&#x2014;",
	"#13"	=>	"&#x203B;",
	"#15"	=>	"&#x003E;",
	"#16"	=>	"&#x03F9;",
	"#17"	=>	"&#x002F;",
	"#18"	=>	"&#x003C;",
	"#19"	=>	"&#x0302;",
	"#21"	=>	"&#x0053;",
	"#22"	=>	"&#x0375;",
	"#23"	=>	"&#x0039;",
	"#24"	=>	"&#x0053;&#x030B;",
	"#29"	=>	"&#x00B7;",
	"#51"	=>	"&#x0387;",
	"#52"	=>	"&#x003A;",
	"#60"	=>	"&#x0399;",
	"#63"	=>	"&#x0394;",
	"#65"	=>	"&#x0397;",
	"#67"	=>	"&#x03A7;",
	"#69"	=>	"&#x039C;",
	"#70"	=>	"&#x002E;",
	"#71"	=>	"&#x0387;",
	"#72"	=>	"&#x02D9;",
	"#73"	=>	"&#x003A;",
	"#75"	=>	"&#x002E;",
	"#80"	=>	"&#x0308;",
	"#81"	=>	"&#x03DB;",
	"#82"	=>	"&#x1FFD;",
	"#83"	=>	"&#x1FEF;",
	"#84"	=>	"&#x1FC0;",
	"#85"	=>	"&#x1FFE;",
	"#86"	=>	"&#x1FBD;",
	"#87"	=>	"&#x0394;&#x0345;",
	"#90"	=>	"&#x2014;",
	"#100"	=>	"&#x00F7;",
	"#103"	=>	"&#x039B;&#x0338;",
	"#118"	=>	"&#x03BB;&#x0338;",
	"#121"	=>	"&#x03BE;&#x0338;",
	"#127"	=>	"&#x03BB;&#x0345;",
	"#129"	=>	"&#x039B;&#x0325;",
	"#130"	=>	"&#x039F;",
	"#132"	=>	"&#x03B2;&#x0338;",
	"#135"	=>	"&#x02D9;",
	"#136"	=>	"&#x03DE;",
	"#150"	=>	"&#x221E;",
	"#151"	=>	"&#x2014;",
	"#156"	=>	"&#x2310;",
	"#161"	=>	"&#x03F7;",
	"#162"	=>	"&#x2610;",
	"#163"	=>	"&#x0375;",
	"#170"	=>	"&#x0049;&#x0049;",
	"#173"	=>	"&#x03F7;",
	"#200"	=>	"&#x2643;",
	"#201"	=>	"&#x2610;",
	"#202"	=>	"&#x264F;",
	"#203"	=>	"&#x264D;",
	"#204"	=>	"&#x2640;",
	"#205"	=>	"&#x2650;",
	"#206"	=>	"&#x2644;",
	"#207"	=>	"&#x2609;",
	"#208"	=>	"&#x263F;",
	"#209"	=>	"&#x263E;",
	"#210"	=>	"&#x2642;",
	"#211"	=>	"&#x2651;",
	"#212"	=>	"&#x264C;",
	"#213"	=>	"&#x2648;",
	"#214"	=>	"&#x264E;",
	"#215"	=>	"&#x264A;",
	"#216"	=>	"&#x264B;",
	"#217"	=>	"&#x2653;",
	"#218"	=>	"&#x2652;",
	"#219"	=>	"&#x2649;",
	"#220"	=>	"&#x260D;",
	"#221"	=>	"&#x263D;",
	"#222"	=>	"&#x260C;",
	"#223"	=>	"&#x2605;",
	"#241"	=>	"&#x260B;",
	"#244"	=>	"&#x264C;",
	"#249"	=>	"&#x03C0;&#x263E;",
	"#303"	=>	"&#x003E;",
	"#319"	=>	"&#x2022;",
	"#320"	=>	"&#x2629;",
	"#321"	=>	"&#x2629;",
	"#322"	=>	"&#x2627;",
	"#323"	=>	"&#x003E;",
	"#451"	=>	"&#x0283;",
	"#458"	=>	"&#x03A7;",
	"#459"	=>	"&#x00B7;",
	"#460"	=>	"&#x2014;",
	"#461"	=>	"&#x007C;",
	"#465"	=>	"&#x2627;",
	"#467"	=>	"&#x2192;",
	"#476"	=>	"&#x0283;",
	"#508"	=>	"&#x203B;",
	"#509"	=>	"&#x0305;&#x0311;",
	"#516"	=>	"&#x0394;&#x0345;",
	"#519"	=>	"&#x2191;",
	"#520"	=>	"&#x2629;",
	"#524"	=>	"&#x2297;",
	"#525"	=>	"&#x271B;",
	"#526"	=>	"&#x2190;",
	"#527"	=>	"&#x02C6;",
	"#528"	=>	"&#x03BB;&#x032D;",
	"#529"	=>	"&#x204B;",
	"#531"	=>	"&#x035E;",
	"#534"	=>	"&#x02C6;",
	"#550"	=>	"&#x2237;",
	"#551"	=>	"&#x25CC;",
	"#556"	=>	"&#x2020;",
	"#561"	=>	"&#x2191;",
	"#562"	=>	"&#x0305;",
	"#563"	=>	"&#x1D242;",
	"#564"	=>	"&#x1D243;",
	"#565"	=>	"&#x1D244;",
	"#566"	=>	"&#x1D231;",
	"#567"	=>	"&#x1D213;",
	"#568"	=>	"&#x1D233;",
	"#569"	=>	"&#x1D236;",
	"#570"	=>	"&#x03F9;",
	"#572"	=>	"&#x1D229;",
	"#573"	=>	"&#x1D212;",
	"#574"	=>	"&#x0393;",
	"#575"	=>	"&#x1D215;",
	"#576"	=>	"&#x1D216;",
	"#577"	=>	"&#x03A6;",
	"#578"	=>	"&#x03A1;",
	"#579"	=>	"&#x039C;",
	"#580"	=>	"&#x0399;",
	"#581"	=>	"&#x0398;",
	"#582"	=>	"&#x1D20D;",
	"#583"	=>	"&#x039D;",
	"#584"	=>	"&#x2127;",
	"#585"	=>	"&#x0396;",
	"#586"	=>	"&#x1D238;",
	"#587"	=>	"&#x0395;",
	"#588"	=>	"&#x1D208;",
	"#589"	=>	"&#x1D21A;",
	"#590"	=>	"&#x1D23F;",
	"#591"	=>	"&#x1D21B;",
	"#592"	=>	"&#x1D240;",
	"#593"	=>	"&#x039B;",
	"#598"	=>	"&#x0394;",
	"#599"	=>	"&#x1D214;",
	"#600"	=>	"&#x1D228;",
	"#602"	=>	"&#x1D237;",
	"#603"	=>	"&#x03A0;",
	"#604"	=>	"&#x1D226;",
	"#615"	=>	"&#x1D230;",
	"#616"	=>	"&#x1D21E;",
	"#617"	=>	"&#x03A9;",
	"#619"	=>	"&#x03BB;",
	"#621"	=>	"&#x1D205;",
	"#622"	=>	"&#x1D201;",
	"#623"	=>	"&#x2127;",
	"#627"	=>	"&#x1D217;",
	"#628"	=>	"&#x039F;",
	"#629"	=>	"&#x039E;",
	"#630"	=>	"&#x0394;",
	"#631"	=>	"&#x039A;",
	"#632"	=>	"&#x1D20E;",
	"#633"	=>	"&#x1D232;",
	"#634"	=>	"&#x1D239;",
	"#635"	=>	"&#x1D200;",
	"#636"	=>	"&#x1D203;",
	"#637"	=>	"&#x1D206;",
	"#638"	=>	"&#x1D209;",
	"#639"	=>	"&#x1D20C;",
	"#640"	=>	"&#x1D211;",
	"#641"	=>	"&#x03A9;",
	"#642"	=>	"&#x0397;",
	"#643"	=>	"&#x1D21D;",
	"#644"	=>	"&#x1D21F;",
	"#645"	=>	"&#x1D221;",
	"#646"	=>	"&#x1D225;",
	"#647"	=>	"&#x1D22C;",
	"#648"	=>	"&#x1D235;",
	"#649"	=>	"&#x1D20B;",
	"#650"	=>	"&#x1D20F;",
	"#651"	=>	"&#x03A7;",
	"#652"	=>	"&#x03A4;",
	"#653"	=>	"&#x1D219;",
	"#654"	=>	"&#x1D21C;",
	"#655"	=>	"&#x1D202;",
	"#656"	=>	"&#x1D224;",
	"#657"	=>	"&#x1D22E;",
	"#658"	=>	"&#x1D23E;",
	"#659"	=>	"&#x1D241;",
	"#660"	=>	"&#x0391;",
	"#661"	=>	"&#x0392;",
	"#662"	=>	"&#x03A5;",
	"#663"	=>	"&#x03A8;",
	"#664"	=>	"&#x1D23A;",
	"#665"	=>	"&#x1D234;",
	"#666"	=>	"&#x1D22F;",
	"#667"	=>	"&#x1D22D;",
	"#668"	=>	"&#x1D210;",
	"#669"	=>	"&#x1D20A;",
	"#670"	=>	"&#x1D207;",
	"#671"	=>	"&#x1D21B;",
	"#672"	=>	"&#x1D218;",
	"#673"	=>	"&#x1D223;",
	"#674"	=>	"&#x1D222;",
	"#675"	=>	"&#x1D240;",
	"#676"	=>	"&#x1D23D;",
	"#677"	=>	"&#x03BC;",
	"#678"	=>	"&#x1D220;",
	"#679"	=>	"&#x1D204;",
	"#683"	=>	"&#x2733;",
	"#684"	=>	"&#x1D22A;",
	"#688"	=>	"&#x03BC;&#x030A;",
	"#703"	=>	"&#x25CB;&#x25CB;&#x25CB;",
	"#709"	=>	"&#x223B;",
	"#710"	=>	"&#x039A;&#x0336;",
	"*#711"	=>	"&#x03FA;",
	"#711"	=>	"&#x03FB;",
	"#722"	=>	"&#x2135;",
	"#723"	=>	"&#x1D50A;",	# This is 1D50A MATHEMATICAL FRAKTUR CAPITAL G. The TLG Unicode chart (quickbeta.pdf) has 1D57E MATHEMATICAL BOLD FRAKTUR CAPITAL G instead; cf. http://www.w3.org/TR/MathML2/bold-fraktur.html.
	"#724"	=>	"&#x210C;",
	"#725"	=>	"&#x1D510;",	# This is 1D510 MATHEMATICAL FRAKTUR CAPITAL M. The TLG Unicode chart (quickbeta.pdf) has 1D578 MATHEMATICAL BOLD FRAKTUR CAPITAL M instead; cf. http://www.w3.org/TR/MathML2/bold-fraktur.html.
	"#751"	=>	"&#x0661;",
	"#752"	=>	"&#x0662;",
	"#753"	=>	"&#x0663;",
	"#754"	=>	"&#x0664;",
	"#755"	=>	"&#x0665;",
	"#756"	=>	"&#x0666;",
	"#757"	=>	"&#x0667;",
	"#758"	=>	"&#x0668;",
	"#759"	=>	"&#x0669;",
	"#760"	=>	"&#x0660;",
	"#762"	=>	"&#x02D9;",
	"#800"	=>	"&#x2733;",
	"#803"	=>	"&#x03A7;",
	"#805"	=>	"&#x03A4;",
	"#811"	=>	"&#x03A4;",
	"#821"	=>	"&#x03A3;",
	"#833"	=>	"&#x039C;",
	"#835"	=>	"&#x03A7;",
	"#836"	=>	"&#x03A3;",
	"#837"	=>	"&#x03A4;",
	"#853"	=>	"&#x0399;",
	"#862"	=>	"&#x0394;",
	"#866"	=>	"&#x03A7;",
	"#922"	=>	"&#x1D228;",
	"#925"	=>	"&#x1D217;",
	"#926"	=>	"&#x1D232;",
	"#927"	=>	"&#x0057;",
	"#928"	=>	"&#x1D20B;",
	"#929"	=>	"&#x1D214;",
	"#932"	=>	"&#x2733;",
	"#939"	=>	"&#x007E;",
	"#941"	=>	"&#x1D205;",
	"#1005"	=>	"&#x03C7;",
	"#1020"	=>	"&#x003C;",
	"#1021"	=>	"&#x0394;&#x0374;",
	"#1022"	=>	"&#x0397;&#x0374;",
	"#1023"	=>	"&#x0399;&#x0374;",
	"#1024"	=>	"&#x039B;&#x0392;",
	"#1100"	=>	"&#x0186;",
	"#1103"	=>	"&#x0323;&#x0313;",
	"#1105"	=>	"&#x004D;&#x030A;",
	"#1109"	=>	"&#x003D;",
	"#1110"	=>	"&#x002D;",
	"#1111"	=>	"&#x00B0;",
	"#1114"	=>	"&#x1D201;",
	"#1115"	=>	"&#x007C;",
	"#1117"	=>	"&#x005A;",
	"#1119"	=>	"&#x0110;",
	"#1121"	=>	"&#x005A;",
	"#1124"	=>	"&#x211E;",
	"#1126"	=>	"&#x004F;",
	"#1127"	=>	"&#x0076;&#x0338;",
	"#1128"	=>	"&#x0049;&#x0336;&#x0049;&#x0336;&#x0053;&#x0336;",
	"#1129"	=>	"&#x005A;&#x0336;",
	"#1130"	=>	"&#x005C;",
	"#1131"	=>	"&#x005C;&#x005C;",
	"#1132"	=>	"&#x005C;&#x0336;",
	"#1133"	=>	"&#x005C;&#x0336;&#x005C;&#x0336;",
	"#1136"	=>	"&#x2112;",
	"#1200"	=>	"&#x00A2;",
	"#1201"	=>	"&#x2021;",
	"#1202"	=>	"&#x20A4;",
	"#1203"	=>	"&#x00DF;",
	"#1204"	=>	"&#x00B0;",
	"#1213"	=>	"&#x0152;",
	"#1214"	=>	"&#x0153;",
	"#1215"	=>	"&#x00C6;",
	"#1216"	=>	"&#x00E6;",
	"#1219"	=>	"&#x0024;",
	"#1220"	=>	"&#x0040;",
	"#1221"	=>	"&#x0131;",
	"#1222"	=>	"&#x0130;",
	"#1223"	=>	"&#x0069;&#x0336;",
	"#1224"	=>	"&#x2295;",
	"#1225"	=>	"&#x00A9;",
	"#1226"	=>	"&#x2731;",
	"#1227"	=>	"&#x2021;",
	"#1230"	=>	"&#x25AD;",
	"#1312"	=>	"&#x004D;&#x0027;",
	"#1313"	=>	"&#x223D;",
	"#1314"	=>	"&#x006E;&#x030A;",
	"#1316"	=>	"&#x0292;",
	"#1317"	=>	"&#x02D9;&#x002F;&#x002F;&#x002E;",
	"#1322"	=>	"&#x2644;",
	"#1323"	=>	"&#x03B6;&#x0337;&#x03C2;&#x0300;",
	"#1324"	=>	"&#x03B8;&#x03C2;&#x0302;",
	"#1335"	=>	"&#x002F;&#x002F;",
	"#1337"	=>	"&#x003E;",
	"#1500"	=>	"&#x03B3;&#x030A;",
	"#1502"	=>	"&#x03A7;&#x0374;",
	"#1512"	=>	"&#x003C;",
	"#1514"	=>	"&#x00F7;",
	"#1518"	=>	"&#x1D229;",
	"#1521"	=>	"&#x0222;",
);

my %betaToUni = (														# There are problems splitting strings on multiple-byte characters that contain backslashes. This is why we're
"A)ß|"	=>	"&#x1F82;",													# using the German sharp s here instead.
"A(ß|"	=>	"&#x1F83;",
"A)/|"	=>	"&#x1F84;",
"A(/|"	=>	"&#x1F85;",
"A)=|"	=>	"&#x1F86;",
"A(=|"	=>	"&#x1F87;",
"Aß|"	=>	"&#x1FB2;",
"A/|"	=>	"&#x1FB4;",
"A=|"	=>	"&#x1FB7;",
"A)|"	=>	"&#x1F80;",
"A(|"	=>	"&#x1F81;",
"A|"	=>	"&#x1FB3;",
"A)ß"	=>	"&#x1F02;",
"A(ß"	=>	"&#x1F03;",
"A)/"	=>	"&#x1F04;",
"A(/"	=>	"&#x1F05;",
"A)="	=>	"&#x1F06;",
"A(="	=>	"&#x1F07;",
"Aß"	=>	"&#x1F70;",
"A/"	=>	"&#x1F71;",
"A="	=>	"&#x1FB6;",
"A)"	=>	"&#x1F00;",
"A("	=>	"&#x1F01;",
"A"	=>	"&#x03B1;",
"*)ßA|"	=>	"&#x1F8A;",
"*(ßA|"	=>	"&#x1F8B;",
"*)/A|"	=>	"&#x1F8C;",
"*(/A|"	=>	"&#x1F8D;",
"*)=A|"	=>	"&#x1F8E;",
"*(=A|"	=>	"&#x1F8F;",
"*)ßA"	=>	"&#x1F0A;",
"*(ßA"	=>	"&#x1F0B;",
"*)/A"	=>	"&#x1F0C;",
"*(/A"	=>	"&#x1F0D;",
"*)=A"	=>	"&#x1F0E;",
"*(=A"	=>	"&#x1F0F;",
"*)A|"	=>	"&#x1F88;",
"*(A|"	=>	"&#x1F89;",
"*)A"	=>	"&#x1F08;",
"*(A"	=>	"&#x1F09;",
"*A"	=>	"&#x0391;",
"B"	=>	"&#x03B2;",
"*B"	=>	"&#x0392;",
"G"	=>	"&#x03B3;",
"*G"	=>	"&#x0393;",
"D"	=>	"&#x03B4;",
"*D"	=>	"&#x0394;",
"E)ß"	=>	"&#x1F12;",
"E(ß"	=>	"&#x1F13;",
"E)/"	=>	"&#x1F14;",
"E(/"	=>	"&#x1F15;",
"Eß"	=>	"&#x1F72;",
"E/"	=>	"&#x1F73;",
"E)"	=>	"&#x1F10;",
"E("	=>	"&#x1F11;",
"E"	=>	"&#x03B5;",
"*)ßE"	=>	"&#x1F1A;",
"*(ßE"	=>	"&#x1F1B;",
"*)/E"	=>	"&#x1F1C;",
"*(/E"	=>	"&#x1F1D;",
"*)E"	=>	"&#x1F18;",
"*(E"	=>	"&#x1F19;",
"*E"	=>	"&#x0395;",
"Z"	=>	"&#x03B6;",
"*Z"	=>	"&#x0396;",
"H)ß|"	=>	"&#x1F92;",
"H(ß|"	=>	"&#x1F93;",
"H)/|"	=>	"&#x1F94;",
"H(/|"	=>	"&#x1F95;",
"H)=|"	=>	"&#x1F96;",
"H(=|"	=>	"&#x1F97;",
"Hß|"	=>	"&#x1FC2;",
"H/|"	=>	"&#x1FC4;",
"H=|"	=>	"&#x1FC7;",
"H)|"	=>	"&#x1F90;",
"H(|"	=>	"&#x1F91;",
"H|"	=>	"&#x1FC3;",
"H)ß"	=>	"&#x1F22;",
"H(ß"	=>	"&#x1F23;",
"H)/"	=>	"&#x1F24;",
"H(/"	=>	"&#x1F25;",
"H)="	=>	"&#x1F26;",
"H(="	=>	"&#x1F27;",
"Hß"	=>	"&#x1F74;",
"H/"	=>	"&#x1F75;",
"H="	=>	"&#x1FC6;",
"H)"	=>	"&#x1F20;",
"H("	=>	"&#x1F21;",
"H"	=>	"&#x03B7;",
"*)ß|H"	=>	"&#x1F9A;",
"*(ß|H"	=>	"&#x1F9B;",
"*)/|H"	=>	"&#x1F9C;",
"*(/|H"	=>	"&#x1F9D;",
"*)=|H"	=>	"&#x1F9E;",
"*(=|H"	=>	"&#x1F9F;",
"*)|H"	=>	"&#x1F98;",
"*(|H"	=>	"&#x1F99;",
"*)ßH"	=>	"&#x1F2A;",
"*(ßH"	=>	"&#x1F2B;",
"*)/H"	=>	"&#x1F2C;",
"*(/H"	=>	"&#x1F2D;",
"*)=H"	=>	"&#x1F2E;",
"*(=H"	=>	"&#x1F2F;",
"*)H"	=>	"&#x1F28;",
"*(H"	=>	"&#x1F29;",
"*H"	=>	"&#x0397;",
"Q"	=>	"&#x03B8;",
"*Q"	=>	"&#x0398;",
"Iß+"	=>	"&#x1FD2;",
"I/+"	=>	"&#x1FD3;",
"I=+"	=>	"&#x1FD7;",
"I+"	=>	"&#x03CA;",
"I)ß"	=>	"&#x1F32;",
"I(ß"	=>	"&#x1F33;",
"I)/"	=>	"&#x1F34;",
"I(/"	=>	"&#x1F35;",
"I)="	=>	"&#x1F36;",
"I(="	=>	"&#x1F37;",
"Iß"	=>	"&#x1F76;",
"I/"	=>	"&#x1F77;",
"I="	=>	"&#x1FD6;",
"I)"	=>	"&#x1F30;",
"I("	=>	"&#x1F31;",
"I"	=>	"&#x03B9;",
"*+I"	=>	"&#x03AA;",
"*)ßI"	=>	"&#x1F3A;",
"*(ßI"	=>	"&#x1F3B;",
"*)/I"	=>	"&#x1F3C;",
"*(/I"	=>	"&#x1F3D;",
"*)=I"	=>	"&#x1F3E;",
"*(=I"	=>	"&#x1F3F;",
"*)I"	=>	"&#x1F38;",
"*(I"	=>	"&#x1F39;",
"*I"	=>	"&#x0399;",
"K"	=>	"&#x03BA;",
"*K"	=>	"&#x039A;",
"L"	=>	"&#x03BB;",
"*L"	=>	"&#x039B;",
"M"	=>	"&#x03BC;",
"*M"	=>	"&#x039C;",
"N"	=>	"&#x03BD;",
"*N"	=>	"&#x039D;",
"C"	=>	"&#x03BE;",
"*C"	=>	"&#x039E;",
"O)ß"	=>	"&#x1F42;",
"O(ß"	=>	"&#x1F43;",
"O)/"	=>	"&#x1F44;",
"O(/"	=>	"&#x1F45;",
"Oß"	=>	"&#x1F78;",
"O/"	=>	"&#x1F79;",
"O)"	=>	"&#x1F40;",
"O("	=>	"&#x1F41;",
"O"	=>	"&#x03BF;",
"*)ßO"	=>	"&#x1F4A;",
"*(ßO"	=>	"&#x1F4B;",
"*)/O"	=>	"&#x1F4C;",
"*(/O"	=>	"&#x1F4D;",
"*)O"	=>	"&#x1F48;",
"*(O"	=>	"&#x1F49;",
"*O"	=>	"&#x039F;",
"P"	=>	"&#x03C0;",
"*P"	=>	"&#x03A0;",
"R"	=>	"&#x03C1;",
"R)"	=>	"&#x1FE4;",
"R("	=>	"&#x1FE5;",
"*R"	=>	"&#x03A1;",
"*(R"	=>	"&#x1FEC;",
"S"	=>	"&#x03C3;",
"S1"	=>	"&#x03C3;",
"S2"	=>	"&#x03C2;",
"S3"	=>	"&#x03F2;",
"*S"	=>	"&#x03A3;",
"*S3"	=>	"&#x03F9;",
"T"	=>	"&#x03C4;",
"*T"	=>	"&#x03A4;",
"Uß+"	=>	"&#x1FE2;",
"U/+"	=>	"&#x1FE3;",
"U=+"	=>	"&#x1FE7;",
"U+"	=>	"&#x03CB;",
"U)ß"	=>	"&#x1F52;",
"U(ß"	=>	"&#x1F53;",
"U)/"	=>	"&#x1F54;",
"U(/"	=>	"&#x1F55;",
"U)="	=>	"&#x1F56;",
"U(="	=>	"&#x1F57;",
"Uß"	=>	"&#x1F7A;",
"U/"	=>	"&#x1F7B;",
"U="	=>	"&#x1FE6;",
"U)"	=>	"&#x1F50;",
"U("	=>	"&#x1F51;",
"U"	=>	"&#x03C5;",
"*+U"	=>	"&#x03AB;",
"*(ßU"	=>	"&#x1F5B;",
"*)/U"	=>	"&#8142;&#933;",
"*(/U"	=>	"&#x1F5D;",
"*(=U"	=>	"&#x1F5F;",
"*(U"	=>	"&#x1F59;",
"*U"	=>	"&#x03A5;",
"*V"	=>	"&#x03DC;",
"V"	=>	"&#x03DD;",
"F"	=>	"&#x03C6;",
"*F"	=>	"&#x03A6;",
"X"	=>	"&#x03C7;",
"*X"	=>	"&#x03A7;",
"Y"	=>	"&#x03C8;",
"*Y"	=>	"&#x03A8;",
"W)ß|"	=>	"&#x1FA2;",
"W(ß|"	=>	"&#x1FA3;",
"W)/|"	=>	"&#x1FA4;",
"W(/|"	=>	"&#x1FA5;",
"W)=|"	=>	"&#x1FA6;",
"W(=|"	=>	"&#x1FA7;",
"Wß|"	=>	"&#x1FF2;",
"W/|"	=>	"&#x1FF4;",
"W=|"	=>	"&#x1FF7;",
"W)|"	=>	"&#x1FA0;",
"W(|"	=>	"&#x1FA1;",
"W|"	=>	"&#x1FF3;",
"W)ß"	=>	"&#x1F62;",
"W(ß"	=>	"&#x1F63;",
"W)/"	=>	"&#x1F64;",
"W(/"	=>	"&#x1F65;",
"W)="	=>	"&#x1F66;",
"W(="	=>	"&#x1F67;",
"Wß"	=>	"&#x1F7C;",
"W/"	=>	"&#x1F7D;",
"W="	=>	"&#x1FF6;",
"W)"	=>	"&#x1F60;",
"W("	=>	"&#x1F61;",
"W"	=>	"&#x03C9;",
"*)ßW|"	=>	"&#x1FAA;",
"*(ßW|"	=>	"&#x1FAB;",
"*)/W|"	=>	"&#x1FAC;",
"*(/W|"	=>	"&#x1FAD;",
"*)=W|"	=>	"&#x1FAE;",
"*(=W|"	=>	"&#x1FAF;",
"*)W|"	=>	"&#x1FA8;",
"*(W|"	=>	"&#x1FA9;",
"*)ßW"	=>	"&#x1F6A;",
"*(ßW"	=>	"&#x1F6B;",
"*)/W"	=>	"&#x1F6C;",
"*(/W"	=>	"&#x1F6D;",
"*)=W"	=>	"&#x1F6E;",
"*(=W"	=>	"&#x1F6F;",
"*)W"	=>	"&#x1F68;",
"*(W"	=>	"&#x1F69;",
"*W"	=>	"&#x03A9;",
"V"	=>	"&#x2032;",
);

my %uniToBeta = (
"&#x03B1;"	=>	"A",	# Alpha
"&#x03B2;"	=>	"B",	# Beta
"&#x03B3;"	=>	"G",	# Gamma
"&#x03B4;"	=>	"D",	# Delta
"&#x03B5;"	=>	"E",	# Epsilon
"&#x03B6;"	=>	"Z",	# Zeta
"&#x03B7;"	=>	"H",	# Eta
"&#x03B8;"	=>	"Q",	# Theta
"&#x03B9;"	=>	"I",	# Iota
"&#x03BA;"	=>	"K",	# Kappa
"&#x03BB;"	=>	"L",	# Lambda
"&#x03BC;"	=>	"M",	# My
"&#x03BD;"	=>	"N",	# Ny
"&#x03BE;"	=>	"C",	# Xi
"&#x03BF;"	=>	"O",	# Omikron
"&#x03C0;"	=>	"P",	# Pi
"&#x03C1;"	=>	"R",	# Rho
"&#x03C2;"	=>	"S",	# Sigma final
"&#x03C3;"	=>	"S",	# Sigma
"&#x03C4;"	=>	"T",	# Tau
"&#x03C5;"	=>	"U",	# Ypsilon
"&#x03C6;"	=>	"F",	# Phi
"&#x03C7;"	=>	"X",	# Chi
"&#x03C8;"	=>	"Y",	# Psi
"&#x03C9;"	=>	"W",	# Omega
"&#945;"	=>	"A",	# Alpha
"&#946;"	=>	"B",	# Beta
"&#947;"	=>	"G",	# Gamma
"&#948;"	=>	"D",	# Delta
"&#949;"	=>	"E",	# Epsilon
"&#950;"	=>	"Z",	# Zeta
"&#951;"	=>	"H",	# Eta
"&#952;"	=>	"Q",	# Theta
"&#953;"	=>	"I",	# Iota
"&#954;"	=>	"K",	# Kappa
"&#955;"	=>	"L",	# Lambda
"&#956;"	=>	"M",	# My
"&#957;"	=>	"N",	# Ny
"&#958;"	=>	"C",	# Xi
"&#959;"	=>	"O",	# Omikron
"&#960;"	=>	"P",	# Pi
"&#961;"	=>	"R",	# Rho
"&#962;"	=>	"S",	# Sigma final
"&#963;"	=>	"S",	# Sigma
"&#964;"	=>	"T",	# Tau
"&#965;"	=>	"U",	# Ypsilon
"&#966;"	=>	"F",	# Phi
"&#967;"	=>	"X",	# Chi
"&#968;"	=>	"Y",	# Psi
"&#969;"	=>	"W",	# Omega
);

my %asciiToBeta = (
"177"	=>	"A",	# Alpha
"178"	=>	"B",	# Beta
"179"	=>	"G",	# Gamma
"180"	=>	"D",	# Delta
"181"	=>	"E",	# Epsilon
"182"	=>	"Z",	# Zeta
"183"	=>	"H",	# Eta
"184"	=>	"Q",	# Theta
"185"	=>	"I",	# Iota
"186"	=>	"K",	# Kappa
"187"	=>	"L",	# Lambda
"188"	=>	"M",	# My
"189"	=>	"N",	# Ny
"190"	=>	"C",	# Xi
"191"	=>	"O",	# Omikron
"128"	=>	"P",	# Pi
"129"	=>	"R",	# Rho
"130"	=>	"S",	# Sigma final
"131"	=>	"S",	# Sigma
"132"	=>	"T",	# Tau
"133"	=>	"U",	# Ypsilon
"134"	=>	"F",	# Phi
"135"	=>	"X",	# Chi
"136"	=>	"Y",	# Psi
"137"	=>	"W",	# Omega
);

my %sygrToBeta = (														# There are problems splitting strings on multiple-byte characters that contain backslashes. This is why we're
"a]/"	=>	"A)ß|",
"a}/"	=>	"A(ß|",
"a[/"	=>	"A)/|",
"a{/"	=>	"A(/|",
"aß/"	=>	"A)=|",
"a|/"	=>	"A(=|",
"a;/"	=>	"Aß|",
"av/"	=>	"A/|",
"a/`"	=>	"A=|",
"aj/"	=>	"A)|",
"aJ/"	=>	"A(|",
"a/"	=>	"A|",
"a]"	=>	"A)ß",
"a}"	=>	"A(ß",
"a["	=>	"A)/",
"a{"	=>	"A(/",
"aß"	=>	"A)=",
"a|"	=>	"A(=",
"a;"	=>	"Aß",
"av"	=>	"A/",
"a`"	=>	"A=",
"aj"	=>	"A)",
"aJ"	=>	"A(",
"a"	=>	"A",
"‘A/"	=>	"*)ßA|",
"]A/"	=>	"*)ßA|",
"’A/"	=>	"*(ßA|",
"}A/"	=>	"*(ßA|",
"“A/"	=>	"*)/A|",
"[A/"	=>	"*)/A|",
"”A/"	=>	"*(/A|",
"{A/"	=>	"*(/A|",
"«A/"	=>	"*)=A|",
"ßA/"	=>	"*)=A|",
"»A/"	=>	"*(=A|",
"|A/"	=>	"*(=A|",
"‘A"	=>	"*)ßA",
"]A"	=>	"*)ßA",
"’A"	=>	"*(ßA",
"}A"	=>	"*(ßA",
"“A"	=>	"*)/A",
"[A"	=>	"*)/A",
"”A"	=>	"*(/A",
"{A"	=>	"*(/A",
"«A"	=>	"*)=A",
"ßA"	=>	"*)=A",
"»A"	=>	"*(=A",
"|A"	=>	"*(=A",
"∆A/"	=>	"*)A|",
"jA/"	=>	"*)A|",
"JA/"	=>	"*(A|",
"∆A"	=>	"*)A",
"jA"	=>	"*)A",
"JA"	=>	"*(A",
"A"	=>	"*A",
"b"	=>	"B",
"B"	=>	"*B",
"g"	=>	"G",
"G"	=>	"*G",
"d"	=>	"D",
"D"	=>	"*D",
"e]"	=>	"E)ß",
"e}"	=>	"E(ß",
"e["	=>	"E)/",
"e{"	=>	"E(/",
"e;"	=>	"Eß",
"ev"	=>	"E/",
"ej"	=>	"E)",
"eJ"	=>	"E(",
"e"	=>	"E",
"‘E"	=>	"*)ßE",
"]E"	=>	"*)ßE",
"’E"	=>	"*(ßE",
"}E"	=>	"*(ßE",
"“E"	=>	"*)/E",
"[E"	=>	"*)/E",
"”E"	=>	"*(/E",
"{E"	=>	"*(/E",
"∆E"	=>	"*)E",
"jE"	=>	"*)E",
"JE"	=>	"*(E",
"E"	=>	"*E",
"z"	=>	"Z",
"Z"	=>	"*Z",
"h/]"	=>	"H)ß|",
"h/}"	=>	"H(ß|",
"h/["	=>	"H)/|",
"h/{"	=>	"H(/|",
"h/ß"	=>	"H)=|",
"h/|"	=>	"H(=|",
"h;/"	=>	"Hß|",
"hv/"	=>	"H/|",
"h/`"	=>	"H=|",
"h/j"	=>	"H)|",
"h/J"	=>	"H(|",
"h/"	=>	"H|",
"h]"	=>	"H)ß",
"h}"	=>	"H(ß",
"h["	=>	"H)/",
"h{"	=>	"H(/",
"hß"	=>	"H)=",
"h|"	=>	"H(=",
"h;"	=>	"Hß",
"hv"	=>	"H/",
"h`"	=>	"H=",
"hj"	=>	"H)",
"hJ"	=>	"H(",
"h"	=>	"H",
"‘H/"	=>	"*)ß|H",
"]H/"	=>	"*)ß|H",
"’H/"	=>	"*(ß|H",
"}H/"	=>	"*(ß|H",
"“H/"	=>	"*)/|H",
"[H/"	=>	"*)/|H",
"”H/"	=>	"*(/|H",
"{H/"	=>	"*(/|H",
"«H/"	=>	"*)=|H",
"ßH/"	=>	"*)=|H",
"»H/"	=>	"*(=|H",
"|H/"	=>	"*(=|H",
"∆H/"	=>	"*)|H",
"jH/"	=>	"*)|H",
"JH/"	=>	"*(|H",
"‘H"	=>	"*)ßH",
"]H"	=>	"*)ßH",
"’H"	=>	"*(ßH",
"}H"	=>	"*(ßH",
"“H"	=>	"*)/H",
"[H"	=>	"*)/H",
"”H"	=>	"*(/H",
"{H"	=>	"*(/H",
"«H"	=>	"*)=H",
"ßH"	=>	"*)=H",
"»H"	=>	"*(=H",
"|H"	=>	"*(=H",
"∆H"	=>	"*)H",
"jH"	=>	"*)H",
"JH"	=>	"*(H",
"H"	=>	"*H",
"q"	=>	"Q",
"Q"	=>	"*Q",
"i÷"	=>	"Iß+",
"i?"	=>	"I/+",
"i¿"	=>	"I=+",
"iü"	=>	"I+",
"i]"	=>	"I)ß",
"i}"	=>	"I(ß",
"i["	=>	"I)/",
"i{"	=>	"I(/",
"iß"	=>	"I)=",
"i|"	=>	"I(=",
"i;"	=>	"Iß",
"iv"	=>	"I/",
"i`"	=>	"I=",
"ij"	=>	"I)",
"iJ"	=>	"I(",
"i"	=>	"I",
"Iü"	=>	"*+I",
"‘I"	=>	"*)ßI",
"]I"	=>	"*)ßI",
"’I"	=>	"*(ßI",
"}I"	=>	"*(ßI",
"“I"	=>	"*)/I",
"[I"	=>	"*)/I",
"”I"	=>	"*(/I",
"{I"	=>	"*(/I",
"«I"	=>	"*)=I",
"ßI"	=>	"*)=I",
"»I"	=>	"*(=I",
"|I"	=>	"*(=I",
"∆I"	=>	"*)I",
"jI"	=>	"*)I",
"JI"	=>	"*(I",
"I"	=>	"*I",
"k"	=>	"K",
"K"	=>	"*K",
"l"	=>	"L",
"L"	=>	"*L",
"m"	=>	"M",
"M"	=>	"*M",
"n"	=>	"N",
"N"	=>	"*N",
"x"	=>	"C",
"X"	=>	"*C",
"o]"	=>	"O)ß",
"o}"	=>	"O(ß",
"o["	=>	"O)/",
"o{"	=>	"O(/",
"o;"	=>	"Oß",
"ov"	=>	"O/",
"oj"	=>	"O)",
"oJ"	=>	"O(",
"o"	=>	"O",
"‘O"	=>	"*)ßO",
"]O"	=>	"*)ßO",
"’O"	=>	"*(ßO",
"}O"	=>	"*(ßO",
"“O"	=>	"*)/O",
"[O"	=>	"*)/O",
"”O"	=>	"*(/O",
"{O"	=>	"*(/O",
"∆O"	=>	"*)O",
"jO"	=>	"*)O",
"JO"	=>	"*(O",
"O"	=>	"*O",
"p"	=>	"P",
"P"	=>	"*P",
"r"	=>	"R",
"rj"	=>	"R)",
"rJ"	=>	"R(",
"R"	=>	"*R",
"JR"	=>	"*(R",
"s"	=>	"S",
'"'	=>	"S",
"~"	=>	"S",
"S"	=>	"*S",
"t"	=>	"T",
"T"	=>	"*T",
"u÷"	=>	"Uß+",
"u?"	=>	"U/+",
"u¿"	=>	"U=+",
"uü"	=>	"U+",
"u]"	=>	"U)ß",
"u}"	=>	"U(ß",
"u["	=>	"U)/",
"u{"	=>	"U(/",
"uß"	=>	"U)=",
"u|"	=>	"U(=",
"u;"	=>	"Uß",
"uv"	=>	"U/",
"u`"	=>	"U=",
"uj"	=>	"U)",
"uJ"	=>	"U(",
"u"	=>	"U",
"Uü"	=>	"*+U",
"’U"	=>	"*(ßU",
"}U"	=>	"*(ßU",
"”U"	=>	"*(/U",
"{U"	=>	"*(/U",
"»U"	=>	"*(=U",
"|U"	=>	"*(=U",
"JU"	=>	"*(U",
"U"	=>	"*U",
"Áü"	=>	"*+U",
"’Á"	=>	"*(ßU",
"}Á"	=>	"*(ßU",
"”Á"	=>	"*(/U",
"{Á"	=>	"*(/U",
"»Á"	=>	"*(=U",
"|Á"	=>	"*(=U",
"JÁ"	=>	"*(U",
"Á"	=>	"*U",
"f"	=>	"F",
"F"	=>	"*F",
"c"	=>	"X",
"C"	=>	"*X",
"y"	=>	"Y",
"Y"	=>	"*Y",
"w]/"	=>	"W)ß|",
"w}/"	=>	"W(ß|",
"w[/"	=>	"W)/|",
"w{/"	=>	"W(/|",
"wß/"	=>	"W)=|",
"w|/"	=>	"W(=|",
"w;/"	=>	"Wß|",
"wv/"	=>	"W/|",
"w/`"	=>	"W=|",
"wj/"	=>	"W)|",
"wJ/"	=>	"W(|",
"w/"	=>	"W|",
"w]"	=>	"W)ß",
"w}"	=>	"W(ß",
"w["	=>	"W)/",
"w{"	=>	"W(/",
"wß"	=>	"W)=",
"w|"	=>	"W(=",
"w;"	=>	"Wß",
"wv"	=>	"W/",
"w`"	=>	"W=",
"wj"	=>	"W)",
"wJ"	=>	"W(",
"w"	=>	"W",
"‘W/"	=>	"*)ßW|",
"]W/"	=>	"*)ßW|",
"’W/"	=>	"*(ßW|",
"}W/"	=>	"*(ßW|",
"“W/"	=>	"*)/W|",
"[W/"	=>	"*)/W|",
"”W/"	=>	"*(/W|",
"{W/"	=>	"*(/W|",
"«W/"	=>	"*)=W|",
"ßW/"	=>	"*)=W|",
"»W/"	=>	"*(=W|",
"|W/"	=>	"*(=W|",
"∆W/"	=>	"*)W|",
"jW/"	=>	"*)W|",
"JW/"	=>	"*(W|",
"‘W"	=>	"*)ßW",
"]W"	=>	"*)ßW",
"’W"	=>	"*(ßW",
"}W"	=>	"*(ßW",
"“W"	=>	"*)/W",
"[W"	=>	"*)/W",
"”W"	=>	"*(/W",
"{W"	=>	"*(/W",
"«W"	=>	"*)=W",
"ßW"	=>	"*)=W",
"»W"	=>	"*(=W",
"|W"	=>	"*(=W",
"∆W"	=>	"*)W",
"jW"	=>	"*)W",
"JW"	=>	"*(W",
"W"	=>	"*W",
":"	=>	":",
"…"	=>	";"
);

my %sgkToBeta = (														# There are problems splitting strings on multiple-byte characters that contain backslashes. This is why we're
"#ƒ"	=>	"A)ß|",
"#‰"	=>	"A)ß|",
"#‘"	=>	"A)ß|",
"#·"	=>	"A(ß|",
"#—"	=>	"A(ß|",
"#¡"	=>	"A(ß|",
"#√"	=>	"A)/|",
"#”"	=>	"A)/|",
"#„"	=>	"A)/|",
"#‡"	=>	"A(/|",
"#¿"	=>	"A(/|",
"#–"	=>	"A(/|",
"#Â"	=>	"A)=|",
"#’"	=>	"A)=|",
"#≈"	=>	"A)=|",
"#“"	=>	"A(=|",
"#‚"	=>	"A(=|",
"#¬"	=>	"A(=|",
"#ßß"	=>	"Aß|",
"#‹"	=>	"Aß|",
"#Ï"	=>	"Aß|",
"#/"	=>	"A/|",
"#ø"	=>	"A/|",
"#Ø"	=>	"A/|",
"#="	=>	"A=|",
"#Ω"	=>	"A=|",
"#Õ"	=>	"A=|",
"#)"	=>	"A)|",
"#π"	=>	"A)|",
"#©"	=>	"A)|",
"#("	=>	"A(|",
"#∏"	=>	"A(|",
"#®"	=>	"A(|",
"#"	=>	"A|",
"aƒ"	=>	"A)ß",
"a‰"	=>	"A)ß",
"a‘"	=>	"A)ß",
"a·"	=>	"A(ß",
"a—"	=>	"A(ß",
"a¡"	=>	"A(ß",
"a√"	=>	"A)/",
"a”"	=>	"A)/",
"a„"	=>	"A)/",
"a‡"	=>	"A(/",
"a¿"	=>	"A(/",
"a–"	=>	"A(/",
"aÂ"	=>	"A)=",
"a’"	=>	"A)=",
"a≈"	=>	"A)=",
"a“"	=>	"A(=",
"a‚"	=>	"A(=",
"a¬"	=>	"A(=",
"aßß"	=>	"Aß",
"a‹"	=>	"Aß",
"aÏ"	=>	"Aß",
"a/"	=>	"A/",
"aø"	=>	"A/",
"aØ"	=>	"A/",
"a="	=>	"A=",
"aΩ"	=>	"A=",
"aÕ"	=>	"A=",
"a)"	=>	"A)",
"aπ"	=>	"A)",
"a©"	=>	"A)",
"a("	=>	"A(",
"a∏"	=>	"A(",
"a®"	=>	"A(",
"a"	=>	"A",
"ƒA"	=>	"*)ßA",
"‰A"	=>	"*)ßA",
"‘A"	=>	"*)ßA",
"·A"	=>	"*(ßA",
"—A"	=>	"*(ßA",
"¡A"	=>	"*(ßA",
"√A"	=>	"*)/A",
"”A"	=>	"*)/A",
"„A"	=>	"*)/A",
"‡A"	=>	"*(/A",
"¿A"	=>	"*(/A",
"–A"	=>	"*(/A",
"ÂA"	=>	"*)=A",
"’A"	=>	"*)=A",
"≈A"	=>	"*)=A",
"“A"	=>	"*(=A",
"‚A"	=>	"*(=A",
"¬A"	=>	"*(=A",
")A"	=>	"*)A",
"πA"	=>	"*)A",
"©A"	=>	"*)A",
"(A"	=>	"*(A",
"∏A"	=>	"*(A",
"®A"	=>	"*(A",
"A"	=>	"*A",
"b"	=>	"B",
"B"	=>	"*B",
"g"	=>	"G",
"G"	=>	"*G",
"d"	=>	"D",
"D"	=>	"*D",
"eƒ"	=>	"E)ß",
"e‰"	=>	"E)ß",
"e‘"	=>	"E)ß",
"e·"	=>	"E(ß",
"e—"	=>	"E(ß",
"e¡"	=>	"E(ß",
"e√"	=>	"E)/",
"e”"	=>	"E)/",
"e„"	=>	"E)/",
"e‡"	=>	"E(/",
"e¿"	=>	"E(/",
"e–"	=>	"E(/",
"eßß"	=>	"Eß",
"e‹"	=>	"Eß",
"eÏ"	=>	"Eß",
"e/"	=>	"E/",
"eø"	=>	"E/",
"eØ"	=>	"E/",
"e)"	=>	"E)",
"eπ"	=>	"E)",
"e©"	=>	"E)",
"e("	=>	"E(",
"e∏"	=>	"E(",
"e®"	=>	"E(",
"e"	=>	"E",
"ƒE"	=>	"*)ßE",
"‰E"	=>	"*)ßE",
"‘E"	=>	"*)ßE",
"·E"	=>	"*(ßE",
"—E"	=>	"*(ßE",
"¡E"	=>	"*(ßE",
"√E"	=>	"*)/E",
"”E"	=>	"*)/E",
"„E"	=>	"*)/E",
"‡E"	=>	"*(/E",
"¿E"	=>	"*(/E",
"–E"	=>	"*(/E",
")E"	=>	"*)E",
"πE"	=>	"*)E",
"©E"	=>	"*)E",
"(E"	=>	"*(E",
"∏E"	=>	"*(E",
"®E"	=>	"*(E",
"E"	=>	"*E",
"z"	=>	"Z",
"Z"	=>	"*Z",
"vƒ"	=>	"H)ß|",
"v‰"	=>	"H)ß|",
"v‘"	=>	"H)ß|",
"v·"	=>	"H(ß|",
"v—"	=>	"H(ß|",
"v¡"	=>	"H(ß|",
"v√"	=>	"H)/|",
"v”"	=>	"H)/|",
"v„"	=>	"H)/|",
"v‡"	=>	"H(/|",
"v¿"	=>	"H(/|",
"v–"	=>	"H(/|",
"vÂ"	=>	"H)=|",
"v’"	=>	"H)=|",
"v≈"	=>	"H)=|",
"v“"	=>	"H(=|",
"v‚"	=>	"H(=|",
"v¬"	=>	"H(=|",
"vßß"	=>	"Hß|",
"v‹"	=>	"Hß|",
"vÏ"	=>	"Hß|",
"v/"	=>	"H/|",
"vø"	=>	"H/|",
"vØ"	=>	"H/|",
"v="	=>	"H=|",
"vΩ"	=>	"H=|",
"vÕ"	=>	"H=|",
"v)"	=>	"H)|",
"vπ"	=>	"H)|",
"v©"	=>	"H)|",
"v("	=>	"H(|",
"v∏"	=>	"H(|",
"v®"	=>	"H(|",
"v"	=>	"H|",
"hƒ"	=>	"H)ß",
"h‰"	=>	"H)ß",
"h‘"	=>	"H)ß",
"h·"	=>	"H(ß",
"h—"	=>	"H(ß",
"h¡"	=>	"H(ß",
"h√"	=>	"H)/",
"h”"	=>	"H)/",
"h„"	=>	"H)/",
"h‡"	=>	"H(/",
"h¿"	=>	"H(/",
"h–"	=>	"H(/",
"hÂ"	=>	"H)=",
"h’"	=>	"H)=",
"h≈"	=>	"H)=",
"h“"	=>	"H(=",
"h‚"	=>	"H(=",
"h¬"	=>	"H(=",
"hßß"	=>	"Hß",
"h‹"	=>	"Hß",
"hÏ"	=>	"Hß",
"h/"	=>	"H/",
"hø"	=>	"H/",
"hØ"	=>	"H/",
"h="	=>	"H=",
"hΩ"	=>	"H=",
"hÕ"	=>	"H=",
"h)"	=>	"H)",
"hπ"	=>	"H)",
"h©"	=>	"H)",
"h("	=>	"H(",
"h∏"	=>	"H(",
"h®"	=>	"H(",
"h"	=>	"H",
"ƒH"	=>	"*)ßH",
"‰H"	=>	"*)ßH",
"‘H"	=>	"*)ßH",
"·H"	=>	"*(ßH",
"—H"	=>	"*(ßH",
"¡H"	=>	"*(ßH",
"√H"	=>	"*)/H",
"”H"	=>	"*)/H",
"„H"	=>	"*)/H",
"‡H"	=>	"*(/H",
"¿H"	=>	"*(/H",
"–H"	=>	"*(/H",
"ÂH"	=>	"*)=H",
"’H"	=>	"*)=H",
"≈H"	=>	"*)=H",
"“H"	=>	"*(=H",
"‚H"	=>	"*(=H",
"¬H"	=>	"*(=H",
")H"	=>	"*)H",
"πH"	=>	"*)H",
"©H"	=>	"*)H",
"(H"	=>	"*(H",
"∏H"	=>	"*(H",
"®H"	=>	"*(H",
"H"	=>	"*H",
"q"	=>	"Q",
"Q"	=>	"*Q",
"ißß+"	=>	"Iß+",
"i‹+"	=>	"Iß+",
"iÏ+"	=>	"Iß+",
"i/+"	=>	"I/+",
"iø+"	=>	"I/+",
"iØ+"	=>	"I/+",
"i=+"	=>	"I=+",
"iΩ+"	=>	"I=+",
"iÕ+"	=>	"I=+",
"i+"	=>	"I+",
"iƒ"	=>	"I)ß",
"i‰"	=>	"I)ß",
"i‘"	=>	"I)ß",
"i·"	=>	"I(ß",
"i—"	=>	"I(ß",
"i¡"	=>	"I(ß",
"i√"	=>	"I)/",
"i”"	=>	"I)/",
"i„"	=>	"I)/",
"i‡"	=>	"I(/",
"i¿"	=>	"I(/",
"i–"	=>	"I(/",
"iÂ"	=>	"I)=",
"i’"	=>	"I)=",
"i≈"	=>	"I)=",
"i“"	=>	"I(=",
"i‚"	=>	"I(=",
"i¬"	=>	"I(=",
"ißß"	=>	"Iß",
"i‹"	=>	"Iß",
"iÏ"	=>	"Iß",
"i/"	=>	"I/",
"iø"	=>	"I/",
"iØ"	=>	"I/",
"i="	=>	"I=",
"iΩ"	=>	"I=",
"iÕ"	=>	"I=",
"i)"	=>	"I)",
"iπ"	=>	"I)",
"i©"	=>	"I)",
"i("	=>	"I(",
"i∏"	=>	"I(",
"i®"	=>	"I(",
"i"	=>	"I",
"+I"	=>	"*+I",
"ƒI"	=>	"*)ßI",
"‰I"	=>	"*)ßI",
"‘I"	=>	"*)ßI",
"·I"	=>	"*(ßI",
"—I"	=>	"*(ßI",
"¡I"	=>	"*(ßI",
"√I"	=>	"*)/I",
"”I"	=>	"*)/I",
"„I"	=>	"*)/I",
"‡I"	=>	"*(/I",
"¿I"	=>	"*(/I",
"–I"	=>	"*(/I",
"ÂI"	=>	"*)=I",
"’I"	=>	"*)=I",
"≈I"	=>	"*)=I",
"“I"	=>	"*(=I",
"‚I"	=>	"*(=I",
"¬I"	=>	"*(=I",
")I"	=>	"*)I",
"πI"	=>	"*)I",
"©I"	=>	"*)I",
"(I"	=>	"*(I",
"∏I"	=>	"*(I",
"®I"	=>	"*(I",
"I"	=>	"*I",
"k"	=>	"K",
"K"	=>	"*K",
"l"	=>	"L",
"L"	=>	"*L",
"m"	=>	"M",
"M"	=>	"*M",
"n"	=>	"N",
"N"	=>	"*N",
"c"	=>	"C",
"C"	=>	"*C",
"oƒ"	=>	"O)ß",
"o‰"	=>	"O)ß",
"o‘"	=>	"O)ß",
"o·"	=>	"O(ß",
"o—"	=>	"O(ß",
"o¡"	=>	"O(ß",
"o√"	=>	"O)/",
"o”"	=>	"O)/",
"o„"	=>	"O)/",
"o‡"	=>	"O(/",
"o¿"	=>	"O(/",
"o–"	=>	"O(/",
"oßß"	=>	"Oß",
"o‹"	=>	"Oß",
"oÏ"	=>	"Oß",
"o/"	=>	"O/",
"oø"	=>	"O/",
"oØ"	=>	"O/",
"o)"	=>	"O)",
"oπ"	=>	"O)",
"o©"	=>	"O)",
"o("	=>	"O(",
"o∏"	=>	"O(",
"o®"	=>	"O(",
"o"	=>	"O",
"ƒO"	=>	"*)ßO",
"‰O"	=>	"*)ßO",
"‘O"	=>	"*)ßO",
"·O"	=>	"*(ßO",
"—O"	=>	"*(ßO",
"¡O"	=>	"*(ßO",
"√O"	=>	"*)/O",
"”O"	=>	"*)/O",
"„O"	=>	"*)/O",
"‡O"	=>	"*(/O",
"¿O"	=>	"*(/O",
"–O"	=>	"*(/O",
")O"	=>	"*)O",
"πO"	=>	"*)O",
"©O"	=>	"*)O",
"(O"	=>	"*(O",
"∏O"	=>	"*(O",
"®O"	=>	"*(O",
"O"	=>	"*O",
"p"	=>	"P",
"P"	=>	"*P",
"r)"	=>	"R)",
"rπ"	=>	"R)",
"r©"	=>	"R)",
"r("	=>	"R(",
"r"	=>	"R",
"(R"	=>	"*(R",
"∏R"	=>	"*(R",
"®R"	=>	"*(R",
"R"	=>	"*R",
"s"	=>	"S",
"º"	=>	"S",
"j"	=>	"S",
"ª"	=>	"S",
"∫"	=>	"S",
"S"	=>	"*S",
"t"	=>	"T",
"T"	=>	"*T",
"ußß+"	=>	"Uß+",
"u‹+"	=>	"Uß+",
"uÏ+"	=>	"Uß+",
"u/+"	=>	"U/+",
"uø+"	=>	"U/+",
"uØ+"	=>	"U/+",
"u=+"	=>	"U=+",
"uΩ+"	=>	"U=+",
"uÕ+"	=>	"U=+",
"u+"	=>	"U+",
"uƒ"	=>	"U)ß",
"u‰"	=>	"U)ß",
"u‘"	=>	"U)ß",
"u·"	=>	"U(ß",
"u—"	=>	"U(ß",
"u¡"	=>	"U(ß",
"u√"	=>	"U)/",
"u”"	=>	"U)/",
"u„"	=>	"U)/",
"u‡"	=>	"U(/",
"u¿"	=>	"U(/",
"u–"	=>	"U(/",
"uÂ"	=>	"U)=",
"u’"	=>	"U)=",
"u≈"	=>	"U)=",
"u“"	=>	"U(=",
"u‚"	=>	"U(=",
"u¬"	=>	"U(=",
"ußß"	=>	"Uß",
"u‹"	=>	"Uß",
"uÏ"	=>	"Uß",
"u/"	=>	"U/",
"uø"	=>	"U/",
"uØ"	=>	"U/",
"u="	=>	"U=",
"uΩ"	=>	"U=",
"uÕ"	=>	"U=",
"u)"	=>	"U)",
"uπ"	=>	"U)",
"u©"	=>	"U)",
"u("	=>	"U(",
"u∏"	=>	"U(",
"u®"	=>	"U(",
"u"	=>	"U",
"+U"	=>	"*+U",
"·U"	=>	"*(ßU",
"—U"	=>	"*(ßU",
"¡U"	=>	"*(ßU",
"√U"	=>	"*)/U",
"¿U"	=>	"*(/U",
"–U"	=>	"*(/U",
"‡U"	=>	"*(/U",
"‚U"	=>	"*(=U",
"¬U"	=>	"*(=U",
"(U"	=>	"*(U",
"∏U"	=>	"*(U",
"®U"	=>	"*(U",
"U"	=>	"*U",
"f"	=>	"F",
"F"	=>	"*F",
"x"	=>	"X",
"X"	=>	"*X",
"y"	=>	"Y",
"Y"	=>	"*Y",
"%ƒ"	=>	"W)ß|",
"%‰"	=>	"W)ß|",
"%‘"	=>	"W)ß|",
"%·"	=>	"W(ß|",
"%—"	=>	"W(ß|",
"%¡"	=>	"W(ß|",
"%√"	=>	"W)/|",
"%”"	=>	"W)/|",
"%„"	=>	"W)/|",
"%‡"	=>	"W(/|",
"%¿"	=>	"W(/|",
"%–"	=>	"W(/|",
"%Â"	=>	"W)=|",
"%’"	=>	"W)=|",
"%≈"	=>	"W)=|",
"%“"	=>	"W(=|",
"%‚"	=>	"W(=|",
"%¬"	=>	"W(=|",
"%ßß"	=>	"Wß|",
"%‹"	=>	"Wß|",
"%Ï"	=>	"Wß|",
"%/"	=>	"W/|",
"%ø"	=>	"W/|",
"%Ø"	=>	"W/|",
"%="	=>	"W=|",
"%Ω"	=>	"W=|",
"%Õ"	=>	"W=|",
"%)"	=>	"W)|",
"%π"	=>	"W)|",
"%©"	=>	"W)|",
"%("	=>	"W(|",
"%∏"	=>	"W(|",
"%®"	=>	"W(|",
"%"	=>	"W|",
"wƒ"	=>	"W)ß",
"w‰"	=>	"W)ß",
"w‘"	=>	"W)ß",
"w·"	=>	"W(ß",
"w—"	=>	"W(ß",
"w¡"	=>	"W(ß",
"w√"	=>	"W)/",
"w”"	=>	"W)/",
"w„"	=>	"W)/",
"w‡"	=>	"W(/",
"w¿"	=>	"W(/",
"w–"	=>	"W(/",
"wÂ"	=>	"W)=",
"w’"	=>	"W)=",
"w≈"	=>	"W)=",
"w“"	=>	"W(=",
"w‚"	=>	"W(=",
"w¬"	=>	"W(=",
"wßß"	=>	"Wß",
"w‹"	=>	"Wß",
"wÏ"	=>	"Wß",
"w/"	=>	"W/",
"wø"	=>	"W/",
"wØ"	=>	"W/",
"w="	=>	"W=",
"wΩ"	=>	"W=",
"wÕ"	=>	"W=",
"w)"	=>	"W)",
"wπ"	=>	"W)",
"w©"	=>	"W)",
"w("	=>	"W(",
"w∏"	=>	"W(",
"w®"	=>	"W(",
"w"	=>	"W",
"ƒW"	=>	"*)ßW",
"‰W"	=>	"*)ßW",
"‘W"	=>	"*)ßW",
"·W"	=>	"*(ßW",
"—W"	=>	"*(ßW",
"¡W"	=>	"*(ßW",
"√W"	=>	"*)/W",
"”W"	=>	"*)/W",
"„W"	=>	"*)/W",
"‡W"	=>	"*(/W",
"¿W"	=>	"*(/W",
"–W"	=>	"*(/W",
"ÂW"	=>	"*)=W",
"’W"	=>	"*)=W",
"≈W"	=>	"*)=W",
"“W"	=>	"*(=W",
"‚W"	=>	"*(=W",
"¬W"	=>	"*(=W",
")W"	=>	"*)W",
"πW"	=>	"*)W",
"©W"	=>	"*)W",
"(W"	=>	"*(W",
"∏W"	=>	"*(W",
"®W"	=>	"*(W",
"W"	=>	"*W",
"ƒ"	=>	")ß",
"‰"	=>	")ß",
"‘"	=>	")ß",
"·"	=>	"(ß",
"—"	=>	"(ß",
"¡"	=>	"(ß",
"√"	=>	")/",
"”"	=>	")/",
"„"	=>	")/",
"‡"	=>	"(/",
"¿"	=>	"(/",
"–"	=>	"(/",
"Â"	=>	")=",
"’"	=>	")=",
"≈"	=>	")=",
"“"	=>	"(=",
"‚"	=>	"(=",
"¬"	=>	"(=",
"ßß"	=>	"ß",
"‹"	=>	"ß",
"Ï"	=>	"ß",
"/"	=>	"/",
"ø"	=>	"/",
"Ø"	=>	"/",
"="	=>	"=",
"Ω"	=>	"=",
"Õ"	=>	"=",
")"	=>	")",
"π"	=>	")",
"©"	=>	")",
"("	=>	"(",
"∏"	=>	"(",
"®"	=>	"(",
":"	=>	":",
";"	=>	";",
"."	=>	".",
","	=>	",",
"'"	=>	"'",
"-"	=>	"-",
"Æ"	=>	"_",
"›"	=>	"V",
"J"	=>	"J",
"?"	=>	"?",
"!"	=>	"!",
"a+"	=>	"a+",
"e+"	=>	"e+",
"o+"	=>	"o+",
"+O"	=>	"+O",
"i∏+"	=>	"I(",
"+"	=>	"+",
"e="	=>	"e",
"o="	=>	"o",
"bßß"	=>	"bßß",
"cßß"	=>	"cßß",
"dßß"	=>	"dßß",
"fßß"	=>	"fßß",
"gßß"	=>	"gßß",
"jßß"	=>	"jßß",
"kßß"	=>	"kßß",
"lßß"	=>	"lßß",
"mßß"	=>	"mßß",
"nßß"	=>	"nßß",
"pßß"	=>	"pßß",
"qßß"	=>	"qßß",
"rßß"	=>	"rßß",
"sßß"	=>	"sßß",
"tßß"	=>	"tßß",
"xßß"	=>	"xßß",
"yßß"	=>	"yßß",
"zßß"	=>	"zßß",
" "	=>	" ",
"„"	=>	"/",
"Ÿ"	=>	"",
"⁄"	=>	"",
"n/"	=>	"n",
"÷"	=>	"<",
"◊"	=>	"<",
"ÿ"	=>	">",
"<2"	=>	"<20",
">2"	=>	">20",
'"'	=>	'"3',
"["	=>	"[",
"]"	=>	"]",
"û"	=>	"[1",
"ü"	=>	"]1",
"<"	=>	"[2",
">"	=>	"]2",
"à"	=>	"[4",
"â"	=>	"]4",
"ß{"	=>	"{",
"ß}"	=>	"}",
"{"	=>	"{",
"}"	=>	"}",
"ù"	=>	"%",
"ö"	=>	"%",
"Ç"	=>	"%2",
"É"	=>	"%3",
"Å"	=>	"%3",
"Ñ"	=>	"%4",
"Ö"	=>	"%5",
"Å"	=>	"%6",
"å"	=>	"%7",
"Ü"	=>	"%6",
"ô"	=>	"%10",
"ã"	=>	"%14",
"»"	=>	"%15",
"é"	=>	"%17",
"¢"	=>	"%32",
"ﬁ"	=>	"%40",
"ﬂ"	=>	"%41",
"æ"	=>	"%43",
"ú"	=>	"#",
"ß"	=>	"#",
"±"	=>	"#1",
"≤"	=>	"#2",
"≥"	=>	"#3",
"µ"	=>	"#5",
"1"	=>	"1",
"2"	=>	"2",
"3"	=>	"3",
"4"	=>	"4",
"5"	=>	"5",
"6"	=>	"6",
"7"	=>	"7",
"8"	=>	"8",
"9"	=>	"9",
"0"	=>	"0",
"ÅÅÇ"	=>	"%2%2%2"
);


# Configuration file separate from this file in order to make setup easier; CGI 16.1 (377), Castro 16.4 (221), Meltzer/Michalski 4.1 (73), cf. 
# CGI.pm 3.8 (143).
# http://www.webreview.com/1998/10_23/developers/10_23_98_2.shtml
# http://www.webreview.com/1998/10_23/developers/database.shtml
# The following lines are adapted from web_store.cgi by Eric Tachibana (Selena Sol) and Gunther Birznieks, available at 
# http://www.extropia.com/

if (-e "QuotationFinderConfig.txt" && -r "QuotationFinderConfig.txt") {	# If the file QuotationFinderConfig.txt exists (in the same directory 
																		# as this script) and is readable, the following block of code is exe-
																		# cuted; Nutshell 4.5.8, Cozens 6.5 (208).
	require "QuotationFinderConfig.txt";								# Imports the configuration file named QuotationFinderConfig.txt; CGI
																		# 16.1 (377). This file is where the server administrator enters such 
																		# information as the path to this file.
} else {																# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
	die "I am sorry but I was unable to require QuotationFinderConfig.txt at line 937 in QuotationFinder-061.cgi. Would you please make sure
		that you have the path correct and that the permissions are set so that I have read access? Thank you.";
																		# Calls the error subroutine and passes an error message to it; CGI 5.5
																		# (116).
	exit;																# Exits the program; Camel3 29.2.35.
}																		# Closes the if... else... block; Nutshell 4.3.

our $quotationFinderDataDir;											# Declares a global variable named quotationFinderDataDir; Camel3 
																		# 4.8.3. The value of this variable is taken from the config file.
our $quotationFinderCss;											# Declares a global variable named quotationFinderCss; Camel3 
																		# 4.8.3. The value of this variable is taken from the config file.
my $q = new CGI;														# Creates a new CGI object and calls it $q; CGI.pm 3.6 (130), CGI 5.1 
																		# (88), 101 17.1 (150). 
my $id					= $q->param('id');								# Uses CGI.pm's param function to access the CGI script's parameter  
my $mo					= $q->param('mo');
my $se					= $q->param('se');								# list, the set of name=value pairs returned by the browser when the 
my $en					= $q->param('en');								# user submits a fill-out form (including hidden fields) or clicks 
my $mt					= $q->param('mt');
my $fo					= $q->param('fo')			|| 'CLCLT';
my $action				= $q->param('action')		|| 'viewNavigation';	# on a URL link containing a query string, and stores the parameters 
my @keys				= $q->param('key');								# in private variables, establishing a default value where necessary; 
my $page				= $q->param('page')			|| '1';				# CGI.pm 5.3 (224, 233), Meltzer/Michalski 4.3 (90), 14.3 (373), CGI 
my $sortOrder			= $q->param('so')			|| 'Total';			# 4.3 (81), 5.2 (95, 96), 11.2 (274).

my $su;
if ($q->request_method() eq 'GET') {									# CGI.pm 2.9 (88); 5.3 (226, 227); CGI 5.2 (92)
																		# We will use the su variable to allow people to get back to where they
	$su = $q->self_url();												# came from (after errors, etc.) What we need is the URL of the last QF
																		# link they clicked (GET method) rather than the last submit button 
} else {																# (POST method). In order to keep the URL while users click form but-
																		# etc., we have to pass it on through hidden fields and access it using
	$su = $q->param('su');												# CGI.pm's param method.
	
}						

my $dbUserFile			= "$quotationFinderDataDir/dbUser.dat";
my $userDir				= get_userDir( $q, $id ) unless ($id eq "");
my $userNameDir			= "$quotationFinderDataDir/$userDir";
my $mldbSearchFile		= "$userNameDir/mldbSearch.dat";

my $searchDir			= get_searchDir( $q, $id, $mo, $se, $en, $mt, $su ) unless ($se eq "");
my $searchNameDir		= "$userNameDir/$searchDir";

my $mldbRefFile			= "$searchNameDir/mldbRef.dat";
my $textFilesDir		= "$searchNameDir/textFiles";
my $mldbTextFiles		= "$searchNameDir/mldbText.dat";
my $dbSeenWorksFile		= "$searchNameDir/dbSeenWorks.dat";
my $dbScoreWorkFile		= "$searchNameDir/dbScoreWork.dat";
my $dbScoreTotalFile	= "$searchNameDir/dbScoreTotal.dat";
my $mldbScoreFile		= "$searchNameDir/mldbScore.dat";

my $qfUrl = $q->url();												# Gets the URL of the current script, minus the additional path infor-
																		# mation and query string, and puts it in the qfUrl variable;
																		# CGI.pm 228f.

$CGI::POST_MAX = 1024 * 800000;											# Limits the total size of the files that can be uploaded at once to 
																		# 800MB; Meltzer/Michalski 7.4 (165), cf. CGI.pm 3.9 (156), CGI 5.2 (99).

#print $q->header;														# Prints the standard header for CGI scripts; CGI.pm 3.6 (130), Nut-
																		# shell 10, Cookbook 19.1. The header tells the Web server what kind of
																		# data it is sending. This line is equivalent to the following line: 
																		# print "Content-type: text/html\n\n";
																		# SOLLTE DIESE ZEILE NICHT BESSER AM ANFANG JEDER print-SUBROUTINE STE-
																		# HEN? CF. CGI 11.2 (276). ABER: COOKBOOK 19.12.
print $q->header(-expires=>'-1d',
				-charset=>'UTF-8');

# The following block of code controls the flow of the program. The conditions of the type "$q->param( 'xyz' )" are met if the user has clicked
# a button named "xyz" (CGI 10.4 [252], 16.1 [381]). The conditions of the type "$action eq 'xyz'" are met if the user has clicked a hypertext 
# link containing the string "action=xyz" (CGI 11.2 [284]).
# WEGEN DER ZEILE my $action = $q->param('action') OBEN KÖNNTEN WIR ALLE BEDINGUNGEN IN DER FORM "$action eq 'xyz'" SCHREIBEN. DAZU MÜSSTEN BEI 
# submit BUTTONS DER name IN action UMBENANNT UND IN DEN BEDINGUNGEN NACH DEM KORRESPONDIERENDEN value GEFRAGT WERDEN. WIR WÜRDEN DANN ABER 
# NICHT MEHR SOFORT SEHEN, OB DIE BEDINGUNGEN VON EINEM BUTTON ODER EINEM LINK HER ERFÜLLT WERDEN. WIR LASSEN ES ALSO IM MOMENT BLEIBEN.
# DIE subroutines WERDEN NICHT MEHR MIT VORANGESTELLTEM AMPERSAND AUFGERUFEN AUFGRUND DER EMPFEHLUNGEN IN CAMEL3 6.2.3.

if ( $q->param( "login" ) ) {											# If a CGI parameter by the name of login exists, the following block 
																		# of code is executed; CGI 16.1 (381). This is the case if a button 
																		# named login has been clicked.
	$id = Check_Login( $q );
	error( $q, "id is an empty string." ) if $id eq "";	# For debugging
	$searchCount = count_search_texts( $q, $id) unless ($id eq "");
	if ($searchCount > 0) {
		print_navigation( $q, $id, $mo );
	} else {
		print_new_refText_name( $q, $id, $mo );	
	}
}
elsif ($action eq "addRefText") {										# Else, if the CGI's action parameter is addRefText, the following block
																		# of code is executed; CGI 11.2 (284). This is the case if a link con-
																		# taining a query string with "action=addRefText" has been clicked.
	print_new_refText_name( $q, $id, $mo, $se, $en, $mt, $su );
}
elsif ( $q->param( "addRefNameSubmit" ) ) {								# Else, if a CGI parameter by the name of addRefNameSubmit exists, the 
																		# following block of code is executed; CGI 16.1 (381). This is the  
																		# case if a button named addRefNameSubmit has been clicked.
	process_refText_name( $q, $id, $mo, $en, $mt, $su );							# We do not pass the se variable to the process_refText_name subroutine,
																		# as a new value for se will be created there.
	print_new_refText( $q, $id, $mo, $se, $en, $mt, $su );
}
elsif ( $q->param( "addRefSubmit" ) ) {									# Else, if a CGI parameter by the name of addRefSubmit exists, the 
																		# following block of code is executed; CGI 16.1 (381). This is the  
																		# case if a button named addRefSubmit has been clicked.
	store_new_refText( $q, $id, $mo, $se, $en, $mt, $su );

	if ($mo eq "ez") {													# If the string stored in the mo variable equals "ez", the following
																		# block of code is executed; Camel3 3.12. In 'Easy mode', users get
																		# to the following directly after submitting a search text.
		print_upload_form( $q, $id, $mo, $se, $en, $mt, $su );							# Calls the print_upload_form subroutine and passes it the q, id, se, 
																		# and en variables; Camel3 6.2, Cookbook 10.0. This form allows users
																		# to choose the file(s) to be searched.
	} else {															# If the condition above is not met, the following block of code is
																		# executed; Camel3 1.6.1.1. In 'Advanced mode', users first get a 
																		# confirmation that their search text was uploaded and an invitation
																		# to call up the navigation page.
		$message = "Search Text Stored";								# Stores the string between quotation marks in a variable named mes-
																		# sage; Camel3 3 1.5.3, 3.17; Cookbook 1.2.
		print_message( $q, $id, $mo, $se, $en, $mt, $su, $message );					# Calls the print_message subroutine and passes it the q, id, se, and 
																		# en variables; Camel3 6.2, Cookbook 10.0.
	}
}															# Close the elsif($action =~ /delete record/i) block. 
elsif ($action eq "chooseRefText") {									# Else, if the CGI's action parameter is chooseRefText, the following
																		# block of code is executed; CGI 11.2 (284). This is the case if a 
																		# link containing a query string with "action=chooseRefText" has been 
																		# clicked.
	$caption="Choose Search Text";						# Sets the value in $caption to Delete Which Word(s).
	$buttonText="Choose Text";						# Sets the value in $buttonText to Delete Word(s). 
	$name="viewNavigation";
	print_refText_list( $caption, $buttonText, $name, $q, $id, $mo, $se, $en, $mt, $su );					# Calls the print_refText_list subroutine and passes it CHECKBOX
}
elsif ($action eq "deleteRefTexts") {									# Else, if the CGI's action parameter is deleteRefTexts, the following
																		# block of code is executed; CGI 11.2 (284). This is the case if a 
																		# link containing a query string with "action=deleteRefTexts" has been
																		# clicked.
	$caption="Delete Which Text(s)?";						# Sets the value in $caption to Delete Which Word(s).
	$buttonText="Delete Text(s)";						# Sets the value in $buttonText to Delete Word(s). 
	$name="deleteRefSubmit";
	print_refText_list( $caption, $buttonText, $name, $q, $id, $mo, $se, $en, $mt, $su );					# Calls the print_refText_list subroutine and passes it CHECKBOX
															# and delete. CHECKBOX and delete are used in the subroutine. 
}															# Closes the elsif($action =~ /delete/i) block; Nutshell 4.3. 
elsif ( $q->param( "deleteRefSubmit" ) ) {								# Else, if a CGI parameter by the name of deleteRefSubmit exists, the 
																		# following block of code is executed; CGI 16.1 (381). This is the  
																		# case if a button named deleteRefSubmit has been clicked.
	$se = delete_refTexts( $q, $id, $mo, $se, $en, $mt, $su );										# Calls the delete_refTexts subroutine. This subroutine will then
															# delete any records whose keys are in the array @key that we read in
															# from the calling Web page.
	$message = "Text(s) Deleted";										# Stores the string between quotation marks in a variable named message;
																		# Camel3 3 1.5.3, 3.17; Cookbook 1.2.
	print_message( $q, $id, $mo, $se, $en, $mt, $su, $message );						# Calls the print_message subroutine and passes it the q, id, se, and en
																		# variables; Camel3 6.2, Cookbook 10.0.
}															# Close the elsif($action =~ /delete record/i) block. 
elsif ($action eq "viewRefText") {										# Else, if the CGI's action parameter is viewRefText, the following
																		# block of code is executed; CGI 11.2 (284). This is the case if a 
																		# link containing a query string with "action=viewRefText" has been
																		# clicked.
	count_refTextWords( $q, $id, $mo, $se, $en, $mt, $su );											# Calls the count_refTextWords subroutine.
	$wordCount = @wordResults;										# Counts the number of matches we found and stores them in
															# $wordCount; Nutshell 4.2.5.
	if ($wordCount > 0) {											# Checks to see if $wordCount is greater than 0. If so, we execute the
															# code inside the block. 
		$caption = "Words in Search Text";						# Sets the value in $caption to "Words in Search Text". 
		$buttonText = "View Navigation Page";					# Sets the value in $buttonText to View Navigation Page. 
		multiple_match( $wordCount, $caption, $buttonText, $q, $id, $mo, $se, $en, $mt, $su );	# Calls the multiple_match subroutine.
		
  	} else {												# Begins an else block in case the above condition failed.
															# Meaning, if there weren't more than 0 matches, we go here. 
		no_match( $q, $id, $mo, $se, $en, $mt, $su );											# Calls the no_match subroutine. 
	}														# Closes the else block; Nutshell 4.3. 
}															# Closes the elsif($action =~ /search/i) block; Nutshell 4.3. 
elsif ($action eq "addRefTextWords") {									# Else, if the CGI's action parameter is addRefTextWords, the following
																		# block of code is executed; CGI 11.2 (284). This is the case if a 
																		# link containing a query string with "action=addRefTextWords" has been
																		# clicked.
	print_add_page( $q, $id, $mo, $se, $en, $mt, $su );										# Order is very important in the if..elsif..else block. If we had moved
															# this block up and made it the first one, then every time we checked for
															# add we would have a match--even if it was supposed to be "add
															# record"! When doing a block like this, always watch what you are
															# matching and match the longest expressions first. 
}
elsif ($action eq "modifyRefTextWords") {								# Else, if the CGI's action parameter is modifyRefTextWords, the follow-
																		# ing block of code is executed; CGI 11.2 (284). This is the case if a 
																		# link containing a query string with "action=modifyRefTextWords" has 
																		# been clicked.
	count_refTextWords( $q, $id, $mo, $se, $en, $mt, $su );											# Calls the count_refTextWords subroutine.
	$wordCount = @wordResults;										# Counts the number of matches the search found and stores the
															# results in $wordCount; Nutshell 4.2.5. 
	if ($wordCount < 1) {										# Checks to see if count was less than one. If so, we didn't find
															# any matches so we execute the code in the block. 
		no_match( $q, $id, $mo, $se, $en, $mt, $su );											# Calls the no_match subroutine to inform the user that their
															# match failed. 
	}														# Closes the if ($wordCount < 1) block; Nutshell 4.3. 
	elsif($wordCount == 1) {									# If the count was not less than 1, we now check to see if $wordCount
															# was equal to 1. If so, we execute the code in the block. Remember that
															# to check the value of a number, we use the double equal ==. If you are
															# checking the value of a string, you would use eq. 
		print_modify_page( $q, $id, $mo, $se, $en, $mt, $su );									# Calls the print_modify_page subroutine. This is the subroutine
															# that displays the selected record on the screen for editing. 
	}														# Closes the if ($wordCount == 1) block; Nutshell 4.3. 
	else {													# If $wordCount wasn't less than 1 and it wasn't equal to 1, it must be
															# more than 1. So, we create an else block that handles this situation. If
															# the if and the elsifs don't evaluate to true, the else is executed. In Perl,
															# you are allowed to have an if..elsif conditional without an else. 
		$caption = "Modify Which Word?";					# Sets the variable $caption to Modify Which Word.
		$buttonText = "Modify Word";						# Sets the variable $buttonText to Modify Word. 
		multiple_match( $wordCount, $caption, $buttonText, $q, $id, $mo, $se, $en, $mt, $su, "RADIO", "modifyRefWordSubmit" );					# Calls the multiple_match subroutine. It passes 2 strings to the
															# subroutine. The first, RADIO, is the type of selection that we show on the
															# HTML page. For modifying, we only want to be able to modify one
															# record at a time--so we use a radio button. Further down, in the delete
															# subroutine, we pass CHECKBOX because multiple record deletes are
															# allowed. 
	}														# Close the else block and the elsif($action =~ /modify/i)
}															# block. 
elsif ( $q->param( "modifyRefWordSubmit" ) ) {							# Else, if a CGI parameter by the name of modifyRefWordSubmit exists, 
																		# the following block of code is executed; CGI 16.1 (381). This is 
																		# the case if a button named modifyRefWordSubmit has been clicked.
	print_modify_page( $q, $id, $mo, $se, $en, $mt, $su );										# Calls the print_modify_page subroutine. There must have been at
															# least one match for us to get here. Actually, there should never be
															# more than one match because we can get to this spot one of two ways.
															# By having only one match from a search OR by clicking a radio button
															# from the multiple match screen. Radio buttons are mutually exclusive
															# so there can only be one chosen at a time. But, if you have multiple
															# records with the same key, then all bets are off because the program
															# has no way of dealing with multiple records having the same key. 
}															# Closes the elsif($action =~ /modify record/i) block; Nutshell 4.3. 
elsif ( $q->param( "storeRefWordSubmit" ) ) {							# Else, if a CGI parameter by the name of storeRefWordSubmit exists, 
																		# the following block of code is executed; CGI 16.1 (381). This is 
																		# the case if a button named storeRefWordSubmit has been clicked.
	store_record( $q, $id, $mo, $se, $en, $mt, $su );							# Calls the store_record subroutine and passes it the value stored in the
															# parameter key that was passed from the calling Web page.
	$message = "Word Stored";											# Stores the string between quotation marks in a variable named mes-
																		# sage; Camel3 3 1.5.3, 3.17; Cookbook 1.2.
	$note = "Note that search results only change after another search using the new word is performed." if (-e "$dbScoreTotalFile");											# If the file whose name is stored in the dbScoreTotalFile variable exists,
																		# Camel 1.5.7, Cozens 6.5 
	print_message( $q, $id, $mo, $se, $en, $mt, $su, $message, $note );						# Calls the print_message subroutine and passes it the q, id, se, and 
																		# en variables; Camel3 6.2, Cookbook 10.0.
}															# Ends the if($action =~ /add record/i) portion of the
															# if..elsif..else block. 
elsif ( $q->param( "storeModifiedRefWordSubmit" ) ) {							# Else, if a CGI parameter by the name of storeModifiedRefWordSubmit exists, 
																		# the following block of code is executed; CGI 16.1 (381). This is 
																		# the case if a button named storeModifiedRefWordSubmit has been clicked.
	store_record( $q, $id, $mo, $se, $en, $mt, $su );							# Calls the store_record subroutine and passes it the value stored in the
															# parameter key that was passed from the calling Web page.
	$message = "Word Stored";											# Stores the string between quotation marks in a variable named mes-
																		# sage; Camel3 3 1.5.3, 3.17; Cookbook 1.2.
	$note = "Note that search results only change after another search using the modified word is performed." if (-e "$dbScoreTotalFile");											# If the file whose name is stored in the dbScoreTotalFile variable exists,
																		# Camel 1.5.7, Cozens 6.5 
	print_message( $q, $id, $mo, $se, $en, $mt, $su, $message, $note );						# Calls the print_message subroutine and passes it the q, id, se, and 
																		# en variables; Camel3 6.2, Cookbook 10.0.
}															# Ends the if($action =~ /add record/i) portion of the
															# if..elsif..else block. 
elsif ($action eq "deleteRefTextWords") {								# Else, if the CGI's action parameter is deleteRefTextWords, the follow-
																		# ing block of code is executed; CGI 11.2 (284). This is the case if a 
																		# link containing a query string with "action=deleteRefTextWords" has 
																		# been clicked.
	count_refTextWords( $q, $id, $mo, $se, $en, $mt, $su );											# Calls the count_refTextWords subroutine.
	$wordCount = @wordResults;										# Counts the number of matches we found and stores them in
															# $wordCount; Nutshell 4.2.5. 
	if ($wordCount < 1)	{							# Calls the no_match subroutine if there was less than one match. 
		no_match($q, $id, $mo, $se, $en, $mt, $su); 
	} else {
		$caption="Delete Which Word(s)?";						# Sets the value in $caption to Delete Which Word(s).
		$buttonText="Delete Word(s)";						# Sets the value in $buttonText to Delete Word(s). 
		multiple_match( $wordCount, $caption, $buttonText, $q, $id, $mo, $se, $en, $mt, $su, "CHECKBOX", "deleteRefWordSubmit");					# Calls the multiple_match subroutine and passes it CHECKBOX
															# and delete. CHECKBOX and delete are used in the subroutine. 
	}
}															# Closes the elsif($action =~ /delete/i) block; Nutshell 4.3. 
elsif ( $q->param( 'deleteRefWordSubmit' ) ) {							# Else, if a CGI parameter by the name of deleteRefWordSubmit exists, 
																		# the following block of code is executed; CGI 16.1 (381). This is 
																		# the case if a button named deleteRefWordSubmit has been clicked.
	delete_refTextWords( $q, $id, $mo, $se, $en, $mt, $su );										# Calls the delete_refTextWords subroutine. This subroutine will then
															# delete any records whose keys are in the array @key that we read in
															# from the calling Web page.
	$message = "Word(s) Deleted";										# Stores the string between quotation marks in a variable named message;
																		# Camel3 3 1.5.3, 3.17; Cookbook 1.2.
	$note = "Note that search results only change after another search without the deleted word(s) is performed." if (-e "$dbScoreTotalFile");											# If the file whose name is stored in the dbScoreTotalFile variable exists,
																		# Camel 1.5.7, Cozens 6.5 
	print_message( $q, $id, $mo, $se, $en, $mt, $su, $message, $note );						# Calls the print_message subroutine and passes it the q, id, se, and 
																		# en variables; Camel3 6.2, Cookbook 10.0.
}															# Close the elsif($action =~ /delete record/i) block. 
elsif ($action eq "newScore") {											# Else, if the CGI's action parameter is newScore, the following block
																		# of code is executed; CGI 11.2 (284). This is the case if a link con-
																		# taining a query string with "action=newScore" has been clicked.
	print_upload_form( $q, $id, $mo, $se, $en, $mt, $su );								# Calls the print_upload_form subroutine and passes it the q, id, se, 
																		# and en variables; Camel3 6.2, Cookbook 10.0.
}															# Close the elsif($action =~ /delete record/i) block. 
elsif ( $q->param( "chooseFileSubmit" ) ) {								# Else, if a CGI parameter by the name of chooseFileSubmit exists, the
																		# following block of code is executed; CGI 16.1 (381). This is the
																		# case if a button named chooseFileSubmit has been clicked.
	get_names( $q, $id, $mo, $se, $en, $mt, $su );
	create_score( $q, $id, $mo, $se, $en, $mt, $su );
}
elsif ( $q->param( "viewScore" ) ) {								# Else, if a CGI parameter by the name of viewScore exists, the
																		# following block of code is executed; CGI 16.1 (381). This is the
																		# case if a button named viewScore has been clicked.
	print_score( $q, $id, $mo, $se, $en, $mt, $su );
}
elsif ($action eq "viewScore") {										# Else, if the CGI's action parameter is viewScore, the following 
																		# block of code is executed; CGI 11.2 (284). This is the case if a 
																		# link containing a query string with "action=viewScore" has been 
																		# clicked.
	print_score( $q, $id, $mo, $se, $en, $mt, $su );
}
elsif ($action eq "viewFilesSearched") {								# Else, if the CGI's action parameter is viewFilesSearched, the fol-
																		# lowing block of code is executed; CGI 11.2 (284). This is the case
																		# if a link containing a query string with "action=viewFilesSearched"
																		# has been clicked.
	print_files_searched( $q, $id, $mo, $se, $en, $mt, $su );
}
elsif ( $q->param( "viewNavigation" ) ) {								# Else, if a CGI parameter by the name of viewNavigation exists, the
																		# following block of code is executed; CGI 16.1 (381). This is the
																		# case if a button named viewNavigation has been clicked.
	print_navigation( $q, $id, $mo, $se );					# We do not pass $en and $mt to the print_navigation subroutine, as these values
															# will be created there by calling sub get_encoding_and_matching.
}
elsif ($action eq "logout") {											# Else, if the CGI's action parameter is logout, the following block
																		# of code is executed; CGI 11.2 (284). This is the case if a link 
																		# containing a query string with "action=logout" has been clicked.
	Logout( $q, $id, $mo, $se, $en, $mt, $su );
}

else { print_login( $q, $id, $mo, $se, $en, $mt, $su ); }									# An else that gets called if none of the above match. In the case,
															# we call the print_navigation subroutine which prints the navigation page for
															# the database.
exit;														# Once we get to this point, we are done with the program. We
															# have gone through all possible conditions and displayed the appropriate
															# page(s) to the user by now. Below this line are all of the functions that
															# perform the various database tasks. 





### Subroutines go below here.


sub print_login {															# Begins the print_login subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine displays the login page to the user.
	$q = shift;														# Shifts the value passed to the subroutine off the @_ array and stores
																		# it in the q variable; Camel 29.2.149.
	# The following JavaScript does form validation; Flanagan 10.3.1 (159), 15.4 (264); CGI.pm 3.12 (176); CGI 7.2 (168)
	
	my $javaScript=<<END;

		function validateLogin()
		{
			var username = this.document.login.username.value;
			var password = this.document.login.password.value;
			var pattern = /[^a-zA-Z0-9]/;
			if (username == null || username == "" || password == null || password == "") {
				alert("Please enter a username and a password. You can enter anything you like as long as it consists of letters and numbers.");
				return false;
			}
			if (pattern.test(username) == 1) {
				alert("In your username, please use only letters a-z/A-Z and numbers.");
				return false;
			}
			if (pattern.test(password) == 1) {
				alert("In your password, please use only letters a-z/A-Z and numbers.");
				return false;
			}
		}
END
	
	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Login',											# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-script=>$javaScript,
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form(
			-name=>'login',
			-onSubmit=>"return validateLogin(this)",
		);

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );												# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
	

															# The next block of code is a here document that prints out some
															# information to the user letting them know that the database did
															# something and provides them with a link out. 
															
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>Login</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Login" target="Help">Help&nbsp;</a></td>
    <td class=roman>Please enter a name and a password of your own choice.<br>
      You will need them if you want to access your search in the future.</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right">Username:</td>
    <td class=roman> 
      <input type="text" name="username" size="40">
    </td>
  </tr>
  <tr> 
    <td class=roman align="right">Password:</td>
    <td class=roman> 
      <input type="text" name="password" size="40">
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Mark if you would like to use QuotationFinder in
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mo' value='ez' checked></td>
    <td class=roman>
      Easy mode or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mo' value='ad'></td>
    <td class=roman>
      Advanced mode.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="login" value="Login">
    </td>
  </tr>
</table>
HTML
	print	$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
#	exit;
	
}																		# Closes the print_login subroutine; Camel3 6.2, Cookbook 10.0.


sub Check_Login{														# Begins the Check_Login subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine checks the username and password against what is stored in
																		# our database.
	$q = shift;															# Shifts the value passed to the subroutine off the @_ array and stores
																		# it in the q variable; Camel 29.2.149.
	my $user = $q->param('username');									# Uses CGI.pm's param function to access the username and password pa-
	my $pass = $q->param('password');									# rameters returned by the browser when the user submits the login 
																		# fill-out form, and stores the parameters in private variables; 
																		# CGI.pm 5.3 (233), CGI 5.2 (96)

	my ($oldDir, %usernames);							# Declares private variables that exist only within the innermost en-
																		# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	if ($user =~ /\W/ or $user =~ /_/ or $pass =~ /\W/ or $pass =~ /_/) {	# If the string contained in the id variable contains a nonword cha-
																		# racter, the following block of code is executed; Nutshell 4.5.7, 
																		# 4.6.4.
		$message = "Please use only letters a-z/A-Z and numbers.";		# Stores a message in the variable named message;
																		# Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit															# Aborts the current subroutine; Camel3 29.2.35.

	} elsif ($user eq "" or $pass eq "") {

		$message = "Please enter a username and a password.<br>"		# Stores a message in the variable named message;
				 . "You can enter anything you like as long as it consists of letters and/or numbers.";		# Stores a message in the variable named message;
																		# Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if ($id =~ /\W/) block; Nutshell 4.3. 
	
	my $id = "$user" . "_" . "$pass";									# Joins ("concatenates") the strings contained in the user and pass va-
																		# riables and stores the results in a private variable named id; Camel3
																		# 1.5.2.

	my $db = tie %userPasses, 'DB_File', $dbUserFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File dbUserFile: $dbUserFile, $!" );
																		# Associates the database file whose path is stored in the dbUserFile
																		# variable with the userPasses hash so that, using the DB_File module, 
																		# any changes to the hash are saved to the file (which is created with
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 435.
	undef $db;															# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	if (exists $userPasses{$id}) {								# If a hash key by the name stored in the id variable already ex-
																		# ists in the userPasses hash, the following block of code is executed; 
																		# Cookbook 5.1.
		$userDir = $userPasses{$id};
		chdir "$quotationFinderDataDir/$userDir" or error( $q, "Can't cd to $quotationFinderDataDir/$userDir: $!\n" );	# Changes the current 
																		# directory to the value stored in the quotationFinderDataDir/userDir 
																		# variables, or calls the error subroutine, passing it a message, if it
																		# can't; Camel3 29.2.9.
	} else {															# If the above condition was not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		$userDir = lc($id);												# Converts the string contained in the id variable into lowercase and
																		# stores the results in the userDir variable; Cookbook 1.9. We convert 
																		# into lowercase because some filesystems are not case sensitive and 
																		# would return an error if we tried to save a file under a name that 
																		# differs only in case.
		$userDir =~ s/[^\w.-]/_/g;										# Gets the value of the userDir variable, substitutes anything that 
																		# is not a word character (letters, digits, underscores), a period, or 
																		# a dash by an underscore, and puts the results back into the userDir 
																		# variable; CGI 5.2 (100), Friedl 7.3.6 (241).
		if ( $userDir =~ /^(\w[\w.-]*)/ ) {								# If the value of the userDir variable starts with a word character and
																		# continues with any number of word characters, periods, and dashes ex-
																		# clusively, the following block of code is executed; CGI 5.2 (100).
			$userDir = $1;												# Stores the text matched by the pattern between the parentheses in the
																		# userDir variable; Nutshell 4.4.5. This move untaints the userDir va- 
																		# riable; CGI 5.2 (102).
		} else {														# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
			$message = "Names must start with a letter or number.";		# Stores a message in the variable named message; Camel3 1.5.3.
			print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);					# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		}																# Closes the if... else... block; Nutshell 4.3.
	
		opendir(DIR, $quotationFinderDataDir) or error( $q, "Can't opendir $quotationFinderDataDir, I'm in Check_Login: $!" );	# Opens the directory by the name 
																		# stored in the quotationFinderDataDir variable for processing and pas-
																		# ses it the directory handle DIR, or calls the error subroutine, pas-
																		# sing it a message, if it can't; Cookbook 9.5, Nutshell 5 Ref.
		while (defined($oldDir = readdir(DIR))) {						# As long as entries are found in the DIR directory, the names are 
																		# stored in the oldDir variable and the following block of code is exe-
																		# cuted; Cookbook 9.5, Camel3 29.2.121.
			 $usernames{$oldDir}++;										# Adds a new element to the usernames hash, using the current value 
																		# of the oldDir variable as the key; Camel3 24.2.1.
		}																# Closes the while loop; Nutshell 4.3.
		closedir(DIR);													# Closes the directory opened by opendir; Camel3 29.2.17.
	
		$userDir =~ s/(\d*)$/($1||0) + 1/e while (exists $usernames{$userDir});
																		# Takes the value stored in the userDir variable, matches any number of
																		# digits followed by the end of the string, and substitutes the whole 
																		# with the results of the matched number (or 0 if there is none) plus 1 
																		# (which gets evaluated) as long as the usernames hash contains a key
																		# by the name of that value; CGI 5.2 (100), Cookbook 5.2, 6.0. The pur- 
																		# pose of this is that in case a folder by that name already exists, 
																		# the new folder's name gets a number attached (or incremented, if 
																		# there already was one) before the suffix so that the old folder does
																		# not get overwritten.
		chdir "$quotationFinderDataDir" or error( $q, "Can't cd to $quotationFinderDataDir: $!\n" );	# Changes the current directory to the 
																		# value stored in the quotationFinderDataDir variable, or calls the er-
																		# ror subroutine, passing it a message, if it can't; Camel3 29.2.9.
		mkdir ($userDir, 0777) or error( $q, "Can't mkdir $userDir: $!" );	# Creates a directory by the name stored in the userDir variable, 
																		# or calls the error subroutine, passing it a message, if it can't; Ca-
																		# mel3 29.2.94.
		$userPasses{$id} = $userDir;								# Adds a new element to the userPasses hash, using the id vari- 
																		# able as the key and the userDir variable as the value; Cookbook 5.1.
		
		untie %userPasses;												# Closes $dbUserFile; Cookbook 14.1, CGI 10.2 (241).
		chdir "$userDir" or error( $q, "Can't cd to $userDir: $!\n" );	# Changes the current directory to the value stored in the userDir va-
																		# riable, or calls the error subroutine, passing it a message, if it 
																		# can't; Camel3 29.2.9.
	}																	# Closes the if... else... block; Nutshell 4.3.
	return $id;
}																		# Closes the Check_Login subroutine; Camel3 6.2, Cookbook 10.0.





sub print_new_refText_name{										# Begins the print_new_refText subroutine; Camel3 6.2, Cookbook 10.0. 
															# This subroutine is the first screen a user sees when they want to add a new 
															# record.
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q, id and se private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).

	# The following JavaScript does form validation; Flanagan 10.3.1 (159), 15.4 (264); CGI.pm 3.12 (176); CGI 7.2 (168)

	my $javaScript=<<END;

		function validateAddRefTextName()
		{
			var refTextName = this.document.newSearchTextName.addRefTextName.value;
			var pattern = /\\W/;
			if (refTextName == null || refTextName == "") {
				alert("Please enter a search text name. You can enter anything you like as long as it consists of letters, numbers, and/or underscores.");
				return false;
			}
			if (pattern.test(refTextName) == 1) {
				alert("Please use letters (a-z/A-Z), numbers, and underscores (_) only.");
				return false;
			}
		}
END

	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'New Search Text Name',								# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-script=>$javaScript,
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form(
			-name=>'newSearchTextName',
			-onSubmit=>"return validateAddRefTextName(this)",
		);

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );													# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
  
															# The following block of code
															# -	Begins a here document. A here document simply prints out
															# 	text until it encounters the terminator that you specify. The
															# 	terminator must be flush to the left side of the program and be on
															# 	the line by itself. Why it was named a here document escapes me. To
															# 	me the name is confusing. I would have called it a print block. 
															# -	Simply prints out HTML for the New Search Text screen.
															# -	Terminates the here document. 
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>New Search Text Name</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Search_Text_Name" target="Help">Help&nbsp;</a></td>
    <td class=roman>Type a name for your search text, choose the CD-ROM to be searched,<br>and click the Use this Search Text Name button.</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right" valign="top">Search Text Name:</td>
    <td class=roman> 
      <input type="text" name="addRefTextName" size="40">
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Mark if you intend to search the
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='en' value='Uni' checked></td>
    <td class=roman>
      TLG or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='en' value='Roman'></td>
    <td class=roman>
      CLCLT.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="addRefNameSubmit" value="Use this Search Text Name">
    </td>
  </tr>
</table>
HTML

	print	$q->hidden(													# We do not pass on a hidden value for "se" to the next form this time.
				-name     => "id",										# The process_refText_name subroutine will create a new se value based 
				-default  => $id,										# on the addRefTextName parameter.  
			),															# CGI 11.2 (278)
			$q->hidden(
				-name     => "mo",										# We do not pass on a hidden value for "se" to the next form either.
				-default  => $mo,										# A new value for en is being created based on the radio button setting
			),															# above.
			$q->hidden(
				-name     => "mt",
				-default  => $mt,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
}																		# Closes the print_new_refText subroutine; Camel3 6.2, Cookbook 10.0.


sub process_refText_name {												# Begins the process_refText_name subroutine; Camel3 6.2, Cookbook 10.0. 
																		# This subroutine takes the new search text from user input and 
																		# stores it in hashes. 
	my ( $q, $id, $mo, $en, $mt, $su ) = @_;										# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277). We do not create a private variable named se in this 
																		# subroutine, as we are about to establish a new value for se that is
																		# to be valid outside of this subroutine as well.
	my $oldDir;							# Declares private variables that exist only within the innermost en-
	my %searchNames;													# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.

	$searchCount = count_search_texts( $q, $id ) unless ($id eq "");

	if ($searchCount == 0 and -e $mldbSearchFile) {						# If the value stored in the searchCount variable is 0 and the file 
																		# whose name is stored in the mldbSearchFile variable exists, the
																		# following block of code is executed; Camel3 3.10. We need the unlink
																		# function here in addition to the one in the delete_refTexts subroutine
																		# as the searchCount can be reduced to 0 not only by delete_refTexts,
																		# but also by count_search_texts. (We can't apply unlink there because
		unlink($mldbSearchFile) or error( $q, "Can't unlink $mldbSearchFile, I'm in process_refText_name: $!");	# Deletes the file whose path is 
																		# stored in the mldbSearchFile variable; Cookbook 9.2. It seems that the 
																		# delete function does not delete the last key of the last entry if all 
																		# entries are to be removed from the multidimensional refTextNames hash.
																		# Simply deleting the corresponding file takes care of that.
	}

	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in process_refText_name." ) if ($userDir eq "");	# For debugging
	my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in process_refText_name: $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile
																		# variable with the refTextNames hash so that, using the MLDBM mo-
																		# dule, any changes to the hash are saved to the file (which is created
																		# with write access for us but no one else in case it doesn't exist 
																		# yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 
																		# 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	$refTextName = $q->param('addRefTextName');							# CGI.pm 232.

	if ($refTextName eq "") {											# If the string contained in the refTextName variable contains a non-
																		# word character, the following block of code is executed; Nutshell
																		# 4.5.7, 4.6.4.
		$message = "Please enter a search text name.<br>"				# Stores a message in the variable named message; # Camel3 1.5.3.
				 . "You can enter anything you like as long as it consists of letters, numbers, and/or underscores.";
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if ($id =~ /\W/) block; Nutshell 4.3. 
	
	elsif ($refTextName =~ /\W/) {										# If the string contained in the refTextName variable contains a non-
																		# word character, the following block of code is executed; Nutshell
																		# 4.5.7, 4.6.4.
		$message = "Please use only letters a-z/A-Z, numbers, and underscores (_).";	# Stores a message in the variable named message;
																		# Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if ($id =~ /\W/) block; Nutshell 4.3. 
	
#	my $namen;														# For debugging.
#
#	foreach $key ( sort keys %refTextNames ) {						# For each key of the refTextNames hash, the following block of code is
#																	# executed with the keys sorted and their names passed to the refTextName 
#																	# variable; Cookbook 5.9, Camel3 4.4.3.	
#		$namen .= "$key, ";											# For debugging.
#		
#	}
#
#
#	error( $q, "namen is $namen");									# For debugging.

	if (exists $refTextNames{$refTextName}) {							# If a hash key by the name stored in the refTextName variable already 
																		# exists in the refTextNames hash, the following block of code is exe- 
																		# cuted; Cookbook 5.1.
		$message = "A search text by that name already exists.<br>Please choose a different name.";	# Stores a message in the variable named 
																		# message; Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if block; Nutshell 4.3.

	$searchDir = lc($refTextName);										# Converts the string contained in the refTextName variable into lower-
																		# case and stores the results in the searchDir variable; Cookbook 1.9.
																		# We convert into lowercase because some filesystems are not case sen-
																		# sitive and would return an error if we tried to save a file under a 
																		# name that differs only in case.
	$searchDir =~ s/[^\w.-]/_/g;										# Gets the value of the searchDir variable, substitutes anything that 
																		# is not a word character (letters, digits, underscores), a period, or 
																		# a dash by an underscore, and puts the results back into the searchDir 
																		# variable; CGI 5.2 (100), Friedl 7.3.6 (241).
	if ( $searchDir =~ /^(\w[\w.-]*)/ ) {								# If the value of the searchDir variable starts with a word character 
																		# and continues with any number of word characters, periods, and dashes 
																		# exclusively, the following block of code is executed; CGI 5.2 (100).
		$searchDir = $1;												# Stores the text matched by the pattern between the parentheses in the
																		# searchDir variable; Nutshell 4.4.5. This move untaints the searchDir 
																		# variable; CGI 5.2 (102).
	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		$message = "You must enter a name that starts with a letter or number.";	# Stores a message in the variable named message; Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if... else... block; Nutshell 4.3.

	$se = $refTextName;													# Assigns the value stored in the refTextName variable to the se vari-
																		# able; Camel3 1.5.3. 
	my $db2 = tie %userPasses, 'DB_File', $dbUserFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File dbUserFile: $dbUserFile, $!" );
																		# Associates the database file whose path is stored in the dbUserFile
																		# variable with the userPasses hash so that, using the DB_File module, 
																		# any changes to the hash are saved to the file (which is created with
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 435.
	undef $db2;															# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	$userDir = $userPasses{$id};
	
	untie %userPasses;													# Closes $dbUserFile; Cookbook 14.1, CGI 10.2 (241).

	error( $q, "userDir is an empty string, id is $id." ) if ($userDir eq "");	# For debugging
	opendir(DIR, "$quotationFinderDataDir/$userDir") or error( $q, "Can't opendir $quotationFinderDataDir/$userDir, I'm in process_refText_name: $!" );	# Opens the directory by the name 
																		# stored in the quotationFinderDataDir variable for processing and pas-
																		# ses it the directory handle DIR, or calls the error subroutine, pas-
																		# sing it a message, if it can't; Cookbook 9.5, Nutshell 5 Ref.
	while (defined($oldDir = readdir(DIR))) {							# As long as entries are found in the DIR directory, the names are 
																		# stored in the oldDir variable and the following block of code is exe-
																		# cuted; Cookbook 9.5, Camel3 29.2.121.
		 $searchNames{$oldDir}++;										# Adds a new element to the searchNames hash, using the current value 
		 																# of the oldDir variable as the key; Camel3 24.2.1.
	}																	# Closes the while loop; Nutshell 4.3.
	closedir(DIR);														# Closes the directory opened by opendir; Camel3 29.2.17.


	$searchDir =~ s/(\d*)$/($1||0) + 1/e while (exists $searchNames{$searchDir});
																		# Takes the value stored in the searchDir variable, matches any number 
																		# of digits followed by the end of the string, and substitutes the 
																		# whole with the results of the matched number (or 0 if there is none) 
																		# plus 1 (which gets evaluated) as long as the searchNames hash con- 
																		# tains a key by the name of that value; CGI 5.2 (100), Cookbook 5.2, 
																		# 6.0. The purpose of this is that in case a folder by that name alrea-
																		# dy exists, the new folder's name gets a number attached (or incremen-
																		# ted, if there already was one) before the suffix so that the old fol-
																		# der does not get overwritten.
	error( $q, "userDir is an empty string, I'm in sub process_refText_name-name." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub process_refText_name-name." ) if ($searchDir eq "");	# For debugging
	mkdir ("$quotationFinderDataDir/$userDir/$searchDir", 0777) or error( $q, "Can't mkdir $searchDir: $!" );	# Creates a directory by the name stored in the searchDir variable,
																		# or calls the error subroutine, passing it a message, if it can't; Ca-
																		# mel3 29.2.94.
	chdir "$quotationFinderDataDir/$userDir/$searchDir" or error( $q, "Can't cd to $searchDir: $!\n" );	# Changes the current directory to the value stored in the searchDir 
																		# variable, or calls the error subroutine, passing it a message, if it 
																		# can't; Camel3 29.2.9.

	$refTextNames{$refTextName} = {										# Adds a new element to the multidimensional refTextNames hash, using the 
		'SearchDir'	=>	$searchDir,										# refTextName variable as the top level key, SearchDir as the lower level
	};																	# key, and the searchDir variable as the latter's value; Camel3 9.4.1.

	untie %refTextNames;												# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).

}																		# Closes the process_refText_name subroutine; Camel3 6.2, Cookbook 10.0.


sub get_userDir {

	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my $db = tie %userPasses, 'DB_File', $dbUserFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File dbUserFile: $dbUserFile, $!" );
																		# Associates the database file whose path is stored in the dbUserFile
																		# variable with the userPasses hash so that, using the DB_File module, 
																		# any changes to the hash are saved to the file (which is created with
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 435.
	undef $db;															# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	$userDir = $userPasses{$id};
	
	untie %userPasses;													# Closes $dbUserFile; Cookbook 14.1, CGI 10.2 (241).

#	error( $q, "userDir is an empty string." ) if $userDir eq "";	# For debugging
	return $userDir;
}																		# Closes the get_userDir subroutine; Camel3 6.2, Cookbook 10.0.


sub count_search_texts{													# Begins the count_search_texts subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine counts the search texts actually stored in their folders
																		# and deletes empty search folders.
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;								# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the variables in the parentheses; Camel3 6.2.1, CGI 11.2 
																		# (277).
	
	# DER FOLGENDE ELEGANTE TRICK FUNKTIONIERT, FÜHRT ABER ANDERSWO ZU EINER STÖRUNG: DIE AUFLISTUNG DER WÄHLBAREN DATEIEN IN CHOOSE BZW. 
	# DELETE SEARCH TEXTS VERSCHWINDET!
	#		count_refText_entries( $q, $id, $mo, $se, $en, $mt, $su );						# Calls the count_refTextWords subroutine and passes it the values
	#																	# between parentheses; Camel3 6.2.
	#		$textCount = @textResults;									# Counts the number of matches we found and stores them in the 
	#																	# $textCount variable; Nutshell 4.2.5. 
	#		print "<p class='small'>textCount = $textCount<br>";		# For debugging.
	#		print "<p class='small'>id = $id<br>";						# For debugging.
	
	my ($search, $datFile, %refTextsSeen);
	
	$searchCount = 0;
	
	$userDir		= get_userDir( $q, $id );
	$userNameDir	= "$quotationFinderDataDir/$userDir";
	return $searchCount unless (-e "$userNameDir/mldbSearch.dat");		# Causes the subroutine to return with the value stored in the 
																		# searchCount variable unless the file named mldbSearch.dat in the 
																		# directory whose name is stored in the userNameDir variable exists; 
																		# Camel3 3.10, 29.2.131. There is no point counting searches if 
																		# mldbSearch.dat doesn't exist, so we return with $searchCount = 0.

	opendir(DIR, $userNameDir) or error( $q, "can't opendir $userNameDir, I'm in count_search_texts 1: $!" );	# Opens the directory by the name 
																		# stored in the userNameDir variable for processing and pas-
																		# ses it the directory handle DIR, or calls the error subroutine, pas-
																		# sing it a message, if it can't; Cookbook 9.0, Nutshell 5 Ref.
my $searchList .= "<br><br>Directory contains the following search folders:";
	while (defined($search = readdir(DIR))) {							# As long as entries are found in the DIR directory, the names are 
																		# stored in the search variable and the following block of code is exe-
																		# cuted; Cookbook 9.5, Camel3 29.2.121.
		if ($search !~ /dbSearch\.dat/ and $search !~ /\.DS_Store/ and $search =~ /\w/) {			# If the value stored in the search variable does not contain the pattern
																		# between the first set of slashes, and does contain the pattern be-
																		# tween the second set (word character), the following block of code 
																		# is executed; Camel3 1.7. We want to ignore Unix . or .. directories as well as our .dat files.
$searchList .= "<br>$search ";
			$searchNameDir	= "$userNameDir/$search";					# Assigns the values stored in the userNameDir and search variables 
																		# to the userNameDir variable, with a slash between them; Camel3 3.8.
			my $oldSearchCount = $searchCount;							# Assigns the value stored in the searchCount variable to the old-
																		# SearchCount variable; Camel3 1.5.3.
			opendir(DIRTWO, $searchNameDir) or error( $q, "can't opendir $searchNameDir, I'm in count_search_texts 2: $!, userNameDir/search is $userNameDir/$search" );	# Opens the directory by the name 
																		# stored in the searchNameDir variable for processing and pas-
																		# ses it the directory handle DIRTWO, or calls the error subroutine, pas-
																		# sing it a message, if it can't; Cookbook 9.0, Nutshell 5 Ref.
			while (defined($datFile = readdir(DIRTWO))) {				# As long as entries are found in the DIRTWO directory, the names are 
																		# stored in the datFile variable and the following block of code is exe-
																		# cuted; Cookbook 9.5, Camel3 29.2.121.
				$searchCount++ if ($datFile =~ /mldbRef\.dat/);			# Auto-increments the value stored in the searchCount variable
																		# if the string stored in the datFile variable matches the pattern
																		# between the slashes; Camel3 1.5.4, 1.7.
				$refTextsSeen{$search} = $searchCount;				# Cookbook 5.1.
#$searchList .= "$searchCount ";
			}															# Closes the while loop; Nutshell 4.3.
			closedir(DIRTWO);											# Closes the directory opened by opendir; Camel3 29.2.17.

			if ($oldSearchCount == $searchCount) {						# If the value contained in the searchCount variable is equal to the 
																		# value contained in the oldSearchCount variable, the following block 
																		# of code is executed; Camel3 3.12. We get here when there was no
																		# mldbRef.dat file in the current search text folder.
				if ($action =~ /^addRefText$|^chooseRefText$|^deleteRefTexts$/) {	# If the content stored in the action variable is 
																		# "addRefText", "chooseRefText", or "deleteRefTexts", the following 
																		# block of code is executed; Camel3 5.1. If a search directory
																		# contains no mldbRef.dat file, we delete it (and the corresponding 
																		# hash entry). Such a directory is created when a user doesn't submit  
																		# a search text after submitting a search text name.
					# No checking if searchDir is an empty string needed here! searchNameDir is built with the search variable above.
					rmtree($searchNameDir);								# Uses the rmtree function of the File::Path module to remove the direc-
																		# tory whose path is stored in the userNameDir and searchDir variables
																		# and all files contained in it; Cookbook 9.8.
					error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in count_search_texts 3." ) if ($userDir eq "");	# For debugging
					my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in count_search_texts 4: $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile
																		# variable with the refTextNames hash so that, using the MLDBM mo-
																		# dule, any changes to the hash are saved to the file (which is created
																		# with write access for us but no one else in case it doesn't exist 
																		# yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 
																		# 435.
					undef $mldb;										# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
					foreach $key (keys %refTextNames) {					# For each key in the refTextNames hash, the following block of code is
																		# executed; Cookbook 5.4. 
						if ($search eq $refTextNames{$key}{'SearchDir'}) {	# If the value stored under the current outer hash key and the 
																		# SearchDir inner hash key in the refTextNames hash is equal to the 
																		# value stored in the search variable, the following block of code
																		# is executed; Camel3 4.3, 1.5.6. We now have a match of a search
																		# directory we have deleted and a corresponding search name we want
																		# to delete from the search name hash.
							delete $refTextNames{$key};					# Deletes from the refTextNames hash the element whose key is stored in 
																		# the key variable; Camel3 29.2.24.
						}												# Closes the if ($search eq $refTextNames{$key}) block; Nutshell 4.3.
					}													# Closes the foreach $key (keys %refTextNames) block; Nutshell 4.3.
					untie %refTextNames;								# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).
				}														# Closes the if ($action =~ /^addRefText...) block; Nutshell 4.3.
			}															# Closes the if ($oldSearchCount == $searchCount) block; Nutshell 4.3.
		}																# Closes the if ($search !~ /dbSearch\.dat/ ... ) block; Nutshell 4.3.
#		print "searchCount = $searchCount\n";							# For debugging.
	}																	# Closes the while (defined($search = readdir(DIR))) block; Nutshell 4.3.
$searchList .= "<br><br>mldbRef.dat files exist in the following folders:";
foreach $key (keys %refTextsSeen) {
	$searchList .= "<br>$key";
}

	closedir(DIR);														# Closes the directory opened by opendir; Camel3 29.2.17.

	$se = "" unless (exists($refTextsSeen{$se}));
	
	if ($action =~ /^addRefText$|^chooseRefText$|^deleteRefTexts$/) {	# If the content stored in the action variable is "addRefText",
																		# "chooseRefText", or "deleteRefTexts", the following block of 
																		# code is executed; Camel3 5.1.

$searchList .= "<br><br>Hash contains the following search text names:";
		error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in count_search_texts 6." ) if ($userDir eq "");	# For debugging
		my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in count_search_texts 7: $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile
																		# variable with the refTextNames hash so that, using the MLDBM mo-
																		# dule, any changes to the hash are saved to the file (which is created
																		# with write access for us but no one else in case it doesn't exist 
																		# yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 
																		# 435.
		undef $mldb;													# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
		foreach $key (keys %refTextNames) {								# For each key in the refTextNames hash, the following block of code is
																		# executed; Cookbook 5.4. 
$searchList .= "<br>$key";
			my $key2 = $refTextNames{$key}{'SearchDir'};				# Takes the value stored under the current outer hash key and the 
																		# SearchDir inner hash key in the refTextNames hash and stores it in 
																		# the private key2 variable; Camel3 9.4.3.
			unless (exists($refTextsSeen{$key2})) {						# Unless there exists an entry in the refTextsSeen hash under the key 
																		# whose value stored in the key variable, the following block of code
																		# is executed; Cookbook 5.2. If we have not found a particular search
																		# in the directories, we want to delete the corresponding entry in the
																		# refTextNames hash.
				delete $refTextNames{$key};								# Deletes from the refTextNames hash the element whose key is stored in 
																		# the key variable; Camel3 29.2.24. While the delete operation above
																		# takes care of folders missing the mldbRef.dat file, this one takes 
																		# care of refTextNames entries missing their corresponding folders.
			}															# Closes the unless (exists($refTextsSeen{$key})) block; Nutshell 4.3.
		}																# Closes the foreach $key (keys %refTextNames) block; Nutshell 4.3.
		untie %refTextNames;											# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).
	}																	# Closes the if ($action eq "chooseRefText") block; Nutshell 4.3.
#error( $q, "$searchList" );
	return $searchCount;
}																		# Closes the count_search_texts subroutine; Camel3 6.2, Cookbook 10.0.


sub get_searchDir {

	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile." ) if ($userDir eq "");	# For debugging
	my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in sub get_searchDir: $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile
																		# variable with the userPasses hash so that, using the MLDBM module, 
																		# any changes to the hash are saved to the file (which is created with
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 435.
	undef $mldb;															# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	my $refTextName = $se;

	$searchDir = $refTextNames{$refTextName}{'SearchDir'};				# Gets the value stored in the refTextNames hash under the refTextName variable 
																		# outer hash key and SearchDir inner hash key, and stores the results in the 
																		# searchDir variable; Camel3 9.4.3.
	
	my $dirList;
	
	if ($searchDir eq "") {
	
		foreach $key ( sort keys %refTextNames ) {						# For each key of the refTextNames hash, the following block of code is
																		# executed with the keys sorted and their names passed to the refTextName 
																		# variable; Cookbook 5.9, Camel3 4.4.3.	
			$searchDir = $refTextNames{$key}{'SearchDir'};				# Gets the value stored in the refTextNames hash under the key variable 
																		# outer hash key and SearchDir inner hash key, and stores the results in the 
																		# searchDir variable; Camel3 9.4.3.
																		
			$dirList .= "$key\t$searchDir<br>";
			if ($searchDir ne "") {
			
				$se = $key;
				
				last;													# Exits the loop; Camel3 4.4.4.
				
			}			
		}
	}
	
#	error( $q, "dirList is $dirList" );
	
	untie %refTextNames;													# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).

	return $searchDir;
}																		# Closes the get_searchDir subroutine; Camel3 6.2, Cookbook 10.0.


sub get_encoding_and_matching {


	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in get_encoding_and_matching." ) if ($userDir eq "");	# For debugging
	my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in get_encoding_and_matching: $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile
																		# variable with the refTextNames hash so that, using the MLDBM module, 
																		# any changes to the hash are saved to the file (which is created with
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 435.
	undef $mldb;															# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	push @enMt, $refTextNames{$se}{'Encoding'};							# Gets the value stored in the refTextNames hash under the se variable 
																		# outer hash key and Encoding inner hash key, and stores the results in the 
																		# enMt array; Camel3 9.4.3.
	push @enMt, $refTextNames{$se}{'Matching'};							# Gets the value stored in the refTextNames hash under the se variable 
																		# outer hash key and Matching inner hash key, and stores the results in the 
																		# enMt array; Camel3 9.4.3.
	untie %refTextNames;													# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).

#	error( $q, "en is an empty string, I'm in get_encoding_and_matching." ) if ($en eq "");	# For debugging
	if (@enMt == 0) {													# If the enMt array is empty, the following block of code is executed; 
																		# Nutshell 4.5.7,4.6.4.
		$message = "You seem to have chosen a Search Text that you had already deleted.<br>";	# Stores a message in the variable named message;
		$message .= "(This can happen after you use your browser's Back button.)";	# Stores a message in the variable named message;
																		# Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if (@enMt == 0) block; Nutshell 4.3. 
	
	return @enMt;														# Passes the values stored in the enMt array back to where the subroutine 
																		# was called; Nutshell 4.7.2.
}																		# Closes the get_encoding_and_matching subroutine; Camel3 6.2, Cookbook 10.0.


sub print_new_refText{										# Begins the print_new_refText subroutine; Camel3 6.2, Cookbook 10.0. 
															# This subroutine is the input screen a user sees when they want to add a new 
															# record.
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).

#	print <<HTML;														# This code has the advantage that new Greek characters are
#		<SCRIPT type="text/javascript">									# inserted where the cursor is. Unfortunately, it is not
#			function storeCaret (textEl) {								# compliant with official JavaScript and does not work with
#				if (textEl.createTextRange) {							# Netscape (as of 7.0).
#					textEl.caretPos = document.selection.createRange().duplicate();					
#				}														# The code can be found in various places on the Internet, e.g.
#			}															# http://www.faqts.com/knowledge_base/view.phtml/aid/1052/fid/130
#			function insertAtCaret (textEl, text) {						# (article by Stefan Vogel and Martin Honnen dated Nov 17, 2000.)
#				if (textEl.createTextRange && textEl.caretPos) {
#					newval = document.virtualKeyboard.addRefText.value
#					var caretPos = textEl.caretPos;
#					caretPos.text = caretPos.text.charAt(caretPos.text.length - 1) == ' ' ? text + ' ' : text;
#				} else {
#					newval = document.virtualKeyboard.addRefText.value
#					textEl.value  = newval + text;
#				}
#				return false;
#			}		
#		</SCRIPT>
#HTML

# Following is a number of JavaScript functions. One makes the result of a clicked link appear in the addRefText HTML textarea.
# It was inspired by http://www.thrall.org/proteus-virtualkb.html; cf. http://home.doramail.com/yuval/greek.htm.
# The other ones do form validation; Flanagan 9.4.1 (141), 10.1.2 (150), 10.3.1 (159), 15.4 (264), III (530); CGI.pm 3.12 (176); CGI 7.2 (168).
# Note that CGI.pm puts CDATA stuff in the HTML around the JavaScripts. Presumably this is needed as CGI.pm also inserts an XML header.

	my $javaScript;
	
	if ($en eq "Roman") {

		$javaScript=<<END;

			function validateAddRefText()
			{
				var string = this.document.newSearchText.addRefText.value;
				var chunks = string.split(/\\s+/);
				var patternW = /\\w/;
				var words = new Array();
				var i = 0;
				for (i in chunks) {
					if (patternW.test(chunks[i]) == 1) {
						words.push(chunks[i]);
					}
				}
				if (words.length < 2) {
					alert("Please enter two words or more.");
					return false;
				}
			}

END

	} else {

		$javaScript=<<END;

			function virtualKeyboard(abcdef) {
				this.document.newSearchText.addRefText.value+=abcdef;
			}

			function validateAddRefText() {
				var string = this.document.newSearchText.addRefText.value;
				var chunks = string.split(/\\s+/);
				var patternW = /\\S/;
				var words = new Array();
				var i = 0;
				var testwords = new Array();
				for (i in chunks) {
					testwords.push(chunks[i]);
					if (patternW.test(chunks[i]) == 1) {
						words.push(chunks[i]);
					}
				}
		//			alert("words is " + words + ", testwords is " + testwords);
		//			return false;
				if (words.length < 2) {
					alert("Please enter two words or more.");
					return false;
				}
			}

END
#//				var pattern = /\\p{IsWord}/;									// Doesn't work
#//				var pattern = /[\u03B1-03C9]/;									// Greek Unicode characters. Breaks Mozilla 1.6b and Opera 6.0.3 for Mac OS X.
#//				if (pattern.test(string) == 1) {
#//					var en = this.document.newSearchText.en.value;
#//					if (en == Beta) {
#//						alert("As you have entered Greek characters, please uncheck the Beta Code checkbox.");
#//						return false;
#//					}
#//				}

	}
	
	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'New Search Text',								# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-script=>$javaScript,
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form(
			-name=>'newSearchText',
			-onSubmit=>"return validateAddRefText(this)",
		);

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );													# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.

															# The following block of code
															# -	Begins a here document. A here document simply prints out
															# 	text until it encounters the terminator that you specify. The
															# 	terminator must be flush to the left side of the program and be on
															# 	the line by itself. Why it was named a here document escapes me. To
															# 	me the name is confusing. I would have called it a print block. 
															# -	Simply prints out HTML for the New Search Text screen.
															# -	Terminates the here document. 
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>New Search Text</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Search_Text" target="Help">Help&nbsp;</a></td>
    <td class=roman>
HTML
      
	if ($en eq "Roman") {
		print <<HTML;
      Type or paste your search text (two words or more) and click the Use this Search Text button.
HTML
	} else {
		print <<HTML;
      Compose your search text (two words or more) by clicking on the Greek letters below.<br>
      Confirm by clicking on the Use this Search Text button.
HTML
	}

#       <br>To enter any other characters, click in the text entry area and use your keyboard.</p>

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right" valign="top">Search Text:</td>
    <td> 
      <textarea name="addRefText" cols="60" rows="4"></textarea>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	unless ($en eq "Roman") {
		print <<HTML;
  <tr>
    <td>&nbsp;</td>
    <td>
      <table>
        <tr>
HTML
		my @greekAlphabet = ("B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF", "C0", "C1", "C3", "C2", "C4", "C5", "C6", "C7", "C8", "C9");
		foreach my $char (@greekAlphabet) {
	#		print "<td><a href=\"#\" onclick=\"return insertAtCaret(virtualKeyboard.addRefText,'&#x03$char;');\">&#x03$char;</a></td>";
	#		print "<td><input type=\"button\" onclick=\"return insertAtCaret(virtualKeyboard.addRefText,'&#x03$char;');\" value=\"&#x03$char;\"></td>";
			print "          <td class=greek><a href=\"javascript:virtualKeyboard('&#x03$char;')\">&#x03$char;</a></td>\n";
		}
		print "          <td class=greek><a href=\"javascript:virtualKeyboard(' ')\">[space]</a></td>\n";
	
		print <<HTML;
        </tr>
      </table>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      You can enter Greek text in <a href='http://www.tlg.uci.edu/BetaCode.html' target='_blank'>Beta Code</a> if you mark the checkbox below.
      <br>Use this option if your browser does not accept Greek Unicode input here.
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='checkbox' name='en' value='Beta'></td>
    <td class=roman>
      Beta Code
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}

	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Mark if your search text consists of
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value='wh' checked></td>
    <td class=roman>
HTML

	if ($en eq "Roman") {

		print <<HTML;
      whole words (e.g. "deposuit potentes"&#151;will match only these forms of "deponere" and "potens"; faster option), or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value='pt'></td>
    <td class=roman>
      parts of words (e.g. "depo poten"&#151;will match "depono," "deposuit," "potens," "potentes," etc.)
HTML

	} else {

		print <<HTML;
      whole words (e.g. "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x03B9;&#x03BB;&#x03B5;&#x03BD; 
      &#x03B4;&#x03C5;&#x03BD;&#x03B1;&#x03C3;&#x03C4;&#x03B1;&#x03C2;</span>"&#151;will match only these forms of 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B1;&#x03B9;&#x03C1;&#x1F73;&#x03C9;</span>" and 
      "<span class=greek>&#x03B4;&#x03C5;&#x03BD;&#x1F71;&#x03C3;&#x03C4;&#x03B7;&#x03C2;</span>"; faster option), or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value='pt'></td>
    <td class=roman>
      parts of words (e.g. "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x03B9;&#x03BB; 
      &#x03B4;&#x03C5;&#x03BD;&#x03B1;&#x03C3;&#x03C4;</span>"&#151;will match 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x1FD6;&#x03BB;&#x03B5;</span>", 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x1FD6;&#x03BB;&#x03B5;&#x03BD;</span>", 
      "<span class=greek>&#x03B4;&#x03C5;&#x03BD;&#x1F71;&#x03C3;&#x03C4;&#x03B7;&#x03BD;</span>", 
      "<span class=greek>&#x03B4;&#x03C5;&#x03BD;&#x1F71;&#x03C3;&#x03C4;&#x03B1;&#x03C2;</span>", etc.)
HTML
	}

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="addRefSubmit" value="Use this Search Text">
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
</table>
HTML
	
	
	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",										# We do not pass on a hidden value for "mt" to the next form either.
				-default  => $en,										# A new value for mt is being created based on the radio button setting
			),															# above.
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
}																		# Closes the print_new_refText subroutine; Camel3 6.2, Cookbook 10.0.


sub store_new_refText {													# Begins the store_new_refText subroutine; Camel3 6.2, Cookbook 10.0. 
																		# This subroutine takes the new search text from user input and 
																		# stores it in hashes. 
#	use bytes;
	
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my ($bigString, $posWordRef, $word, $key);				# Declares private variables that exist only within the innermost en-
																		# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.

	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in sub store_new_refText." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub store_new_refText." ) if ($searchDir eq "");
	my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in store_new_refText: $!" );
	my $mldb2 = tie %refText, 'MLDBM', $mldbRefFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbRefFile is $mldbRefFile $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile/
																		# dbRefFile/mldbRefFile variable with the refTextNames hash so that, 
																		# using the DB_File module, any changes to the hash are saved to the 
																		# file (which is created with write access for us but no one else in 
																		# case it doesn't exist yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 
																		# (32), 2.9 (51), Cozens 435.

	undef $mldb;														# Frees up the memory associated with the objects; Camel3 29.2.187, 
	undef $mldb2;														# Cookbook 11.0.
	
	$posWordRef = 0;													# Sets the variable posWordRef, which we will use as a counter, to 0;
																		# Learning 4.4.
	$refTextNames{$se} = {												# Adds a new entry to the multidimensional refTextNames hash, with $se as 
		'Encoding'		=>	$en,										# the outher hash key, Encoding as the inner hash key, and the en variable
		'Matching'		=>	$mt,
		'SearchDir'		=>	$searchDir,
	};																	# as its value; Camel3 9.4.1.


#	$refTextNames{$se}{'Encoding'} = $en;								# The technique used above overwrites the SearchDir entry. I did this
																		# because for some reason, the usual technique for adding entries in
																		# multidimensional hashes didn't work; Camel3 9.4.1, Advanced 2.2.1, 
																		# 1.3.2.

	$bigString = $q->param('addRefText');					# CGI.pm 232.
	$bigString =~ tr/@//d if ($en eq "Beta");							# Deletes all at marks in the string contained in the bigString vari-
																		# able if the string contained in the en variable equals Beta; Camel3
																		# 5.2.4, Nutshell 4.3.1.4.
#error( $q, "bigString is $bigString" );
	my @words = split " ", $bigString;									# Camel3 29.2.161.
	
my $testString;

	if ($en eq "Roman") {

		foreach my $wordIn (@words) {
			++$posWordRef;												# Adds one to the word position counter $posWordRef; Learning 2.6.2.
			my $word = lc($wordIn);										# Converts the string stored in the wordIn variable to lowercase and 
																		# stores it in the word variable; Cookbook 1.9.
			$word =~ s/[^a-z]//g;										# Removes from the content of the word variable all characters except
																		# for a-z; Camel3 5.4.1.
			$word =~ tr/vj/ui/;											# Replaces every occurrence of v and j by u and i, respectively; Camel3
																		# 5.2.4, CLCLT-3 manual, p. 64.
			$key = $posWordRef;											# Puts the current value of posWordRef in a variable named key; Camel3
																		# 1.5.3. We will use the position the current word has in the reference
																		# text as the key with which we will look up information on that word.
			$refText{$key} = {											# Adds a new entry to the multidimensional refText hash, with $key as 
				'PosWordRef'	=>	$posWordRef,								# the key and $word as the value of the Word string as well as the 
				'GenFreq'		=>	100,								# the key and $word as the value of the Word string as well as the 
				'Word'			=>	$word,								# first value of the Forms and the Cognates arrays, and 100 as the va-
				'Forms'			=>	[ $word ],							# lue of the GenFreq entry; Cookbook 5.1, Camel 4.7.5.1, Camel3 2.9, 
				'Cognates'		=>	[ $word ],							# 9.6. The user will be able to add more values to the Forms and Cog-
			};															# nates arrays and change the GenFreq value later.
		}

	} elsif ($en eq "Uni") {

		foreach my $wordUni (@words) {
			$testString .= " ";

#			while ($wordUni =~ /(.)/g) { # . is never a newline here
#				$testString .= "while loop: Dollar1 is '$1'<br>\n";				# $_ immer blank...
#			}

			my $wordBeta;
#			my @chars = split (/(&#\w+?;)/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/(\p{IsWord})/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/()/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/(\\u\w\w\w\w)/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/(\w)/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/./, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/(\x{3B1})/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/(.)/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/(\x03B1)/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
#			my @chars = split (/(\x03B1)/, $wordUni);					# Splits up the string stored in the word variable into individual Uni- 
																		# code characters and puts them in the chars array; Cookbook 1.5.
			my @chars = unpack("C*", $wordUni);							# Cookbook 1.5. In Perl 5.8.1 funktioniert split nicht wie gewünscht 
																		# mit Unicode-Zeichen.
#			error( $q, "unicode word character matched") if $wordUni =~ /\p{IsWord}/;	# Funktioniert!!!!!
#			error( $q, "unicode greek matched") if $wordUni =~ /\\p{In_Greek}/;
#			error( $q, "unicode alpha matched") if $wordUni =~ /\x03B1/;
			
#			$testString .= "wordUni is '$wordUni'<br>\n";
#			$wordUni =~ tr/\0-\x{10ffff}/\0-\xff?/;
#			$testString .= "latin1word is '$wordUni'<br>\n";


#			if ($wordUni =~ /(\p{IsWord})/) {							# funktioniert!!!
#				error( $q, "'\p{IsWord}' is matched, Dollar1 is '$1'")
#			}
#			if ($wordUni =~ /\w/) {										# funktioniert nicht
#				error( $q, "'\\w' is matched")
#			}
#			if ($wordUni =~ /./) {										# funktioniert!!!
#				error( $q, "'.' is matched")
#			}
#			if ($wordUni =~ /\x{3B1}/) {										# funktioniert nicht
#				error( $q, "'\\x{3B1}' is matched")
#			}
			
			my $gatekeeper;
			for my $char (@chars) {
				$testString .= "char is '$char', ";
#				$char = ord($char);
#				$testString .= "ordchar is '$char', ";
				next unless ($char);									# Skip the rest of the block unless the value stored in the char variable 
																		# is a true value, i.e. not an empty string; Cookbook 1.0.
#				my $betaChar = $uniToBeta{$char};
#				$testString .= "betaChar is '$betaChar'<br>\n";
#				$wordBeta .= $betaChar if ($betaChar);					# Cookbook 1.0.

				if ($char eq "206" or $char eq "207") {
				
					$gatekeeper = "off";
					next;
					
				}
				
				if ($gatekeeper eq "off") {

					my $betaChar = $asciiToBeta{$char};
					$testString .= "betaChar is '$betaChar'<br>\n";
					$wordBeta .= $betaChar if ($betaChar);					# Cookbook 1.0.
					$gatekeeper = "on";
					
				}
			}

			if ($wordBeta) {											# Cookbook 1.0.

				++$posWordRef;												# Adds one to the word position counter $posWordRef; Learning 2.6.2.
				$key = $posWordRef;										# Puts the current value of posWordRef in a variable named key; Camel3
																		# 1.5.3. We will use the position the current word has in the reference
																		# text as the key with which we will look up information on that word.
				$refText{$key} = {										# Adds a new entry to the multidimensional refText hash, with $key as 
					'PosWordRef'=>	$posWordRef,								# the key and $word as the value of the Word string as well as the 
					'GenFreq'	=>	100,								# the key and $word as the value of the Word string as well as the 
					'Word'		=>	$wordBeta,							# first value of the Forms and the Cognates arrays, and 100 as the va-
					'Forms'		=>	[ $wordBeta ],						# lue of the GenFreq entry; Cookbook 5.1, Camel 4.7.5.1, Camel3 2.9, 
					'Cognates'	=>	[ $wordBeta ],						# 9.6. The user will be able to add more values to the Forms and Cog-
				};														# nates arrays and change the GenFreq value later.
			}															# Closes the if ($wordBeta) block; Nutshell 4.3.
		}

	} elsif ($en eq "Beta") {

		foreach my $wordIn (@words) {
		#	$testString .= " ";
			my $wordBeta  = uc($wordIn);								# Turns all characters stored in the wordIn variable into uppercase and 
																		# saves them in the wordBeta variable; Cookbook 1.9.
			$wordBeta =~ s/[^A-Z]//g;									# Removes from the content of the wordBeta variable all characters ex- 
																		# cept for A-Z; Camel3 5.4.1.

			if ($wordBeta) {											# Cookbook 1.0.

				++$posWordRef;											# Adds one to the word position counter $posWordRef; Learning 2.6.2.

				$key = $posWordRef;										# Puts the current value of posWordRef in a variable named key; Camel3
																		# 1.5.3. We will use the position the current word has in the reference
																		# text as the key with which we will look up information on that word.
				$refText{$key} = {										# Adds a new entry to the multidimensional refText hash, with $key as 
					'PosWordRef'=>	$posWordRef,								# the key and $word as the value of the Word string as well as the 
					'GenFreq'	=>	100,								# the key and $word as the value of the Word string as well as the 
					'Word'		=>	$wordBeta,							# first value of the Forms and the Cognates arrays, and 100 as the va-
					'Forms'		=>	[ $wordBeta ],						# lue of the GenFreq entry; Cookbook 5.1, Camel 4.7.5.1, Camel3 2.9, 
					'Cognates'	=>	[ $wordBeta ],						# 9.6. The user will be able to add more values to the Forms and Cog-
				};														# nates arrays and change the GenFreq value later.
			}															# Closes the if ($wordBeta) block; Nutshell 4.3.
		}
	} else {
		error( $q, "en is $en") 
	}
	
#	error( $q, "testString is:<br>\n$testString" );
		
	my @keys = keys %refText;											# Camel3 29.2.79.
	my $keyNumber = @keys;
	
	unless ($keyNumber > 1) {											# Camel3 3.11.

		$searchDir = $refTextNames{$se}{'SearchDir'};						# Gets the value stored in the refTextNames hash under the se variable 
																		# top level key and SearchDir lower level key, and stores the results in the 
																		# searchDir variable; Camel3 9.4.3.
		rmtree("$userNameDir/$searchDir") if ($searchDir);				# Uses the rmtree function of the File::Path module to remove the direc-
																		# tory whose path is stored in the userNameDir and searchDir variables
																		# and all directories and files contained in it; Cookbook 1.0, 9.8.
		delete $refTextNames{$se};										# Deletes the $se entry from the refTextNames hash; Cookbook 5.3.
	}

	if ($keyNumber == 0) {

		$message = "QuotationFinder has not received a Search Text.";

		if ($en eq "Uni") {
			$message .= "<br>If you entered a text by clicking on the Greek letters,"
					 .	"<br>your browser does not accept Greek Unicode input here."
					 .	"<br>Please use Beta Code instead."
					 .	"<br>If you entered Roman letters, you probably forgot to "
					 .	"<br>check the Beta Code checkbox.";
		}

		$se = "";														# Assigns an empty string to the se variable; Camel3 1.5.3. We remove the 
																		# name of the search here so that the program won't try to find a search 
																		# that never got stored.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);					# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;

	} elsif ($keyNumber == 1) {

		$message = "QuotationFinder has only received a single word."
				 .	"<br>Please enter a text of two words or more.";

		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);					# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;
	}
	
	untie %refText;														# Closes $mldbRefFile; Cookbook 14.1, CGI 10.2 (241).
	untie %refTextNames;												# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).

}																		# Closes the store_new_refText subroutine; Camel3 6.2, Cookbook 10.0.


sub print_refText_list{

	my ( $caption, $buttonText, $name, $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to private variables; Camel3 6.2.1, 
																		# CGI 11.2 (277).
#	my $refTextName;														# Declares private variables that exist only within innermost enclosing
#	my $description;													# block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.

	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Search Texts',									# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form;

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );												# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.

#error( $q, "id is empty string") if $id eq "";
#get_userDir( $q, $id, $mo, $se, $en, $mt, $su );
#$mldbSearchFile	= "$quotationFinderDataDir/$userDir/mldbSearch.dat";
	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in print_refText_list." ) if ($userDir eq "");	# For debugging
	my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in print_refText_list: $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile
																		# variable with the refTextNames hash so that, using the MLDBM mo-
																		# dule, any changes to the hash are saved to the file (which is created
																		# with write access for us but no one else in case it doesn't exist 
																		# yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 
																		# 435.
	undef $mldb;															# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	if (scalar keys %refTextNames < 1) {								# If the number of keys of the refTextNames hash is less than 1, the 
																		# following block of code is executed; Camel3 2.9.
		$message = "You seem to have chosen a Search Text that you had already deleted.<br>";	# Stores a message in the variable named message;
		$message .= "(This can happen after you use your browser's Back button.)";	# Stores a message in the variable named message;
																		# Camel3 1.5.3.
#		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>$caption</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Search_Text" target="Help">Help&nbsp;</a></td>
    <td class=roman>
      $message
    </td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="viewNavigation" value="View Navigation Page">
    </td>
  </tr>
</table>
HTML
		print	$q->hidden(												# CGI 11.2 (278)
					-name     => "id",
					-default  => $id,
				),
				$q->hidden(
					-name     => "mo",
					-default  => $mo,
				),
				$q->hidden(
					-name     => "se",
					-default  => $se,
				),
				$q->hidden(
					-name     => "en",
					-default  => $en,
				),
				$q->hidden(
					-name     => "su",
					-default  => $su,
				),
				$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
				$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
		exit															# Aborts the current subroutine; Camel3 29.2.35.
	
	}																	# Closes the if block; Nutshell 4.3.



#	my $population;														# For debugging
#	for my $family ( keys %refTextNames ) {
#		$population .=  "$family: ";
#		for my $role ( keys %{ $refTextNames{$family} } ) {
#			 $population .= "$role = $refTextNames{$family}{$role} ";
#		}
#		$population .= "<br>";
#	}
#	error( $q, "population is <br>$population" );

	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>$caption</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Search_Text" target="Help">Help&nbsp;</a></td>
    <td class=roman>
HTML

	if (scalar(keys(%refTextNames)) == 1) {								# If the number of keys of the refTextNames hash is equal to 1, the 
																		# following block of code is executed; Camel3 2.9.
		print <<HTML;
      One search text is stored in QuotationFinder.<br>
      Select it and click $buttonText.
HTML

	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		print <<HTML;
      Make your choice and click $buttonText.
HTML

	}																	# Closes the if... else... block; Nutshell 4.3.
		print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
HTML

	foreach $key ( sort keys %refTextNames ) {						# For each key of the refTextNames hash, the following block of code is
																		# executed with the keys sorted and their names passed to the refTextName 
																		# variable; Cookbook 5.9, Camel3 4.4.3.
		if ($caption =~ /(Delete)/) {					# Checks to see if @_ contains more than 6 items and the 8th item 
																		# passed to the subroutine, $_[7], was modify or delete--if so, we 
																		# execute the code inside of the block. 
															#
															# On this line, we specify input type=$_[5].... Remember that when we
															# called this subroutine, the first thing we passed it was RADIO or
															# CHECKBOX. This is what determines what type of HTML input field is

			print <<HTML;
    <td class=roman align="right"> 
      <input type=checkbox name=key value=$key>
    </td>
HTML
		} else {
			print <<HTML;
    <td class=roman align="right"> 
      <input type=radio name=se value=$key>
    </td>
HTML
		} 																# Closes the if ($caption =~ /(Delete)/) block; Nutshell 4.3.		

		print <<HTML;
    <td class=roman>
      $key
    </td>
  </tr>
  <tr> 
HTML
 	}																	# Closes the foreach loop; Nutshell 4.3.
 	
	print <<HTML;
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      <input type="submit" name="$name" value="$buttonText">
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	unless ($caption =~ /(Delete)/) {
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      To delete search texts click <a href='$qfUrl?action=deleteRefTexts&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>here</a>.
    </td>
  </tr>
HTML
 	}																	# Closes the unless block; Nutshell 4.3.
 	
	print <<HTML;
</table>
HTML

	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			);
	if ($caption =~ /(Delete)/) {
		print $q->hidden(
				-name     => "se",
				-default  => $se,
			);
	}
	print	$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).

	untie %refTextNames;												# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).
}																		# Closes the print_files_searched subroutine; Camel3 6.2, Cookbook 
																		# 10.0.

sub delete_refTexts{													# Begins the delete_refTexts subroutine; Camel3 6.2, Cookbook 10.0. This
																		# subroutine performs user-selected deletions of search directories and of 
																		# corresponding entries from the reference text name hash.
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;											# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1,
																		# CGI 11.2 (277).
	my ($current, $searchDir, $deleteCount);							# Declares a private variable that exists only within the innermost en-
																		# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	
	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in sub delete_refTexts." ) if ($userDir eq "");	# For debugging
	my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in delete_refTexts: $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile
																		# variable with the refTextNames hash so that, using the MLDBM mo-
																		# dule, any changes to the hash are saved to the file (which is created
																		# with write access for us but no one else in case it doesn't exist 
																		# yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 (32), 2.9 (51), Cozens 
																		# 435.
	undef $mldb;															# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	$searchCount = scalar(keys(%refTextNames));							# Gets the number of keys in the refTextNames hash and stores it in the
																		# searchCount variable; Camel3 2.9.
	foreach $key (keys %refTextNames) {									# For each key in the refTextNames hash, the following block of code is
																		# executed; Cookbook 5.4. 
		foreach $current (@keys) {										# For each value (stored in $current) of the keys array, the following
																		# block of code is executed; Cookbook 4.4. The keys array is the values
																		# of all of the checkboxes that were checked on the calling Web page.
			if ($current eq $key) {										# If $current is equal to $key, the following block of code is execu-
																		# ted; Camel3 4.3, 1.5.6. We now have a match of a delete checkbox mark
																		# and a search text hash key.
				$searchDir = $refTextNames{$key}{'SearchDir'};			# Gets the value stored in the refTextNames hash under the key variable 
																		# top level key and SearchDir lower level key, and stores the results in 
																		# the searchDir variable; Camel3 9.4.3.
#				error( $q, "searchDir is an empty string, current is $current, I'm in delete_refTexts" ) if ($searchDir eq "");
				if ($searchDir eq "") {
					$message = "You seem to have chosen a Search Text that you had already deleted.<br>";	# Stores a message in the variable named message;
					$message .= "(This can happen after you use your browser's Back button.)";	# Stores a message in the variable named message;
																					# Camel3 1.5.3.
					print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																					# parentheses; Camel3 6.2, 6.2.3.
					exit;															# Aborts the current subroutine; Camel3 29.2.35.
				}
				rmtree("$userNameDir/$searchDir");						# Uses the rmtree function of the File::Path module to remove the direc-
																		# tory whose path is stored in the userNameDir and searchDir variables
																		# and all directories and files contained in it; Cookbook 9.8.
				delete $refTextNames{$key};								# Deletes the $key entry from the refTextNames hash; Cookbook 5.3.

				++$deleteCount;

				param(-name=>'se', -value=>'') if ($key eq $se);		# Sets the se parameter to an empty string if the value stored in the 
											# NÜTZT NICHTS ?????		# key variable equals the one in the se variable; CGI.pm 5.4 (232).  
																		# If one of the search texts being deleted is the current search text,
																		# we need to remove its name from the current search text parameter.
				$se = "" if ($key eq $se);	# NÜTZT NICHTS ?????
			}															# Closes the if block; Nutshell 4.3.
		}																# Closes the foreach loop that goes through @keys; Nutshell 4.3.
	}																	# Closes the foreach loop that goes through %refTextNames; Nutshell 
																		# 4.3.
	if ($deleteCount >= $searchCount) {
		unlink($mldbSearchFile) or error( $q, "Can't unlink $mldbSearchFile, I'm in delete_refTexts: $!");	# Deletes the file whose path is stored in the mldbSearchFile 
																		# variable; Cookbook 9.2. If a user deletes all searches, we delete the 
																		# file that lists them. It seems that the delete function above does 
																		# not delete the last key of the last entry if all entries are to be 
																		# removed from the multidimensional refTextNames hash. Simply deleting 
																		# the corresponding file takes care of that.
	}
	
	untie %refTextNames;												# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).

	return $se;															# Causes the subroutine to return with the se variable; Camel3 29.2.131. 

}																		# Closes the delete_refTexts subroutine; Camel3 6.2, Cookbook 10.0.


sub store_record {														# Begins the store_record subroutine; Camel3 6.2, Cookbook 10.0. This
																		# subroutine takes user input and stores it in search text hashes.

	my ( $q, $id, $mo, $se ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q, id, mo, and se private variables, respectively; Camel3 6.2.1,
																		# CGI 11.2 (277).
																# We do not pass $en and $mt to this subroutine, as CGI parameters for en and mt
																# are being passed on from forms.
	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in sub store_record." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub store_record." ) if ($searchDir eq "");
	my $mldb = tie %refTextNames, 'MLDBM', $mldbSearchFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in sub store_record: $!" );
	my $mldb2 = tie %refText, 'MLDBM', $mldbRefFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbRefFile is $mldbRefFile $!" );
																		# Associates the database file whose path is stored in the mldbSearchFile/
																		# dbRefFile/mldbRefFile variable with the refTextNames hash so that, 
																		# using the DB_File module, any changes to the hash are saved to the 
																		# file (which is created with write access for us but no one else in 
																		# case it doesn't exist yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 
																		# (32), 2.9 (51), Cozens 435.
	undef $mldb;														# Frees up the memory associated with the objects; Camel3 29.2.187, 
	undef $mldb2;														# Cookbook 11.0.
	
	$refTextNames{$se} = {												# Adds a new entry to the multidimensional refTextNames hash, with $se as 
		'Encoding'		=>	$en,										# the outher hash key, Encoding as the inner hash key, and the en variable
		'Matching'		=>	$mt,
		'SearchDir'		=>	$searchDir,
	};																	# as its value; Camel3 9.4.1.

	my $key			= $keys[0] || time();			# Gets the key that was stored in a hidden field by the multiple_match subroutine
#	my $key			= $q->param('key') || time();			# Gets the key that was stored in a hidden field by the multiple_match subroutine
															# if the store_record subroutine was called after modifying a record. If not, it
															# grabs the system time. We use this as the key field in the database for all
															# records added "by hand", i.e. not by the store_new_refText subroutine.

	my $posWordRef		= $q->param('PosWordRef');					# CGI.pm 232.
	my $genFreq			= $q->param('GenFreq');					# CGI.pm 232.
	my $wordIn			= $q->param('Word');					# CGI.pm 232.
	my $formString		= $q->param('Forms');					# CGI.pm 232.
	my $cognateString	= $q->param('Cognates');					# CGI.pm 232.
	
	my ($word, $form, $cognate);												# Declares private variables that exist only within the innermost en-
	my (@forms, @cognates);												# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.

	$wordIn =~ s/^\s+//;												# Removes leading and trailing whitespace; Cookbook 1.14.
	$wordIn =~ s/\s+$//; 
	
	if ($wordIn =~ /\s/) {												# If the string contained in the wordIn variable contains a white-
																		# space character, the following block of code is executed; Nutshell
																		# 4.5.7, 4.6.4.
		$message = "The 'Word' field cannot contain more than one word."	# Stores a message in the variable named message;
																		# Camel3 1.5.3.
				 . "<p>Use the Forms and Cognates fields instead, or use the Add a Word function "
				 . "<br>repeatedly to create a separate entry for every word."
				 . "<p>For further explanations click <a href=\"/QuotationFinderHelp.html#Fill_Fields\" target=\"Help\">here</a>.";

		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);					# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;

	}
	
	if ($posWordRef =~ /\D/) {											# If the string contained in the posWordRef variable contains a non-
																		# digit character, the following block of code is executed; Nutshell
																		# 4.5.7, 4.6.4.
		$message = "Please only use a number (integer) in the Position field."	# Stores a message in the variable named message;
																		# Camel3 1.5.3.
				 . "<p>Simply number the words in your Search Text up to the position"
				 . "<br>where the added word occurs, or leave the field blank.";

		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);					# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;

	}

	$posWordRef = 1 if ($posWordRef eq "");								# Stores the value 1 in the variable named posWordRef if the value pre-
																		# viously stored there is an empty string; Camel3 1.5. We need to avoid
																		# "uninitialized values" in case users leave the position field blank.	
	if ($genFreq =~ /\D/) {												# If the string contained in the genFreq variable contains a non-
																		# digit character, the following block of code is executed; Nutshell
																		# 4.5.7, 4.6.4.
		$message = "Please only use a number (integer) in the Frequency field."	# Stores a message in the variable named message;
																		# Camel3 1.5.3.
				 . "<p>This is for you to indicate how many times the word occurs in the CD-ROM"
				 . "<br>you are about to search. You may leave the field blank."
				 . "<p>For further explanations click <a href=\"/QuotationFinderHelp.html#Fill_Fields\" target=\"Help\">here</a>.";

		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);					# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;

	}

	$genFreq = 100 if ($genFreq eq "");									# Stores the value 100 in the variable named genFreq if the value pre-
																		# viously stored there is an empty string; Camel3 1.5. We need to avoid
																		# "uninitialized values" in case users leave the frequency field blank.	
	if ($en eq "Roman") {
	
		$word = lc($wordIn);											# Converts the string stored in the wordIn variable to lowercase and 
																		# stores it in the word variable; Cookbook 1.9.
		$word =~ s/[^a-z]//g;											# Removes from the content of the word variable all characters except
																		# for a-z; Camel3 5.4.1.
		$word =~ tr/vj/ui/;												# Replaces every occurrence of v and j by u and i, respectively; Camel3
																		# 5.2.4, CLCLT-3 manual, p. 64.
		@forms = split " ", $formString;								# Camel3 29.2.161.
	
		foreach my $form (@forms) {

			$form = lc($form);											# Converts the string stored in the form variable to lowercase and 
																		# stores it back in the form variable; Cookbook 1.9.
			$form =~ s/[^a-z]//g;										# Removes from the content of the form variable all characters except
																		# for a-z; Camel3 5.4.1.
			$form =~ tr/vj/ui/;											# Replaces every occurrence of v and j by u and i, respectively; Camel3
																		# 5.2.4, CLCLT-3 manual, p. 64.
		}

		@cognates = split " ", $cognateString;							# Camel3 29.2.161.
	
		foreach my $cognate (@cognates) {

			$cognate = lc($cognate);									# Converts the string stored in the cognate variable to lowercase and 
																		# stores it back in the cognate variable; Cookbook 1.9.
			$cognate =~ s/[^a-z]//g;									# Removes from the content of the cognate variable all characters except
																		# for a-z; Camel3 5.4.1.
			$cognate =~ tr/vj/ui/;										# Replaces every occurrence of v and j by u and i, respectively; Camel3
																		# 5.2.4, CLCLT-3 manual, p. 64.
		}

	} elsif ($en eq "Uni") {
	
		my $wordUni = $wordIn;

#		my @chars = split (/(&#\w+?;)/, $wordUni);						# Splits up the string stored in the wordUni variable into individual  
#																		# Unicode characters and puts them in the chars array; Cookbook 1.5.
		my @chars = unpack("C*", $wordUni);								# Cookbook 1.5. In Perl 5.8.1 funktioniert split nicht wie gewünscht 
																		# mit Unicode-Zeichen.


		my $gatekeeper;
		for my $char (@chars) {
			next unless ($char);										# Skip the rest of the block unless the value stored in the char variable 
																		# is a true value, i.e. not an empty string; Cookbook 1.0.
#			my $betaChar = $uniToBeta{$char};
#			$word .= $betaChar if ($betaChar);							# Cookbook 1.0.
			if ($char eq "206" or $char eq "207") {
			
				$gatekeeper = "off";
				next;
				
			}
			
			if ($gatekeeper eq "off") {

				my $betaChar = $asciiToBeta{$char};
				$word .= $betaChar if ($betaChar);						# Cookbook 1.0.
				$gatekeeper = "on";
				
			}

		}
		
		my @formsUni = split " ", $formString;							# Camel3 29.2.161.
	
		foreach my $formUni (@formsUni) {

#			my @chars = split (/(&#\w+?;)/, $formUni);					# Splits up the string stored in the formUni variable into individual  
#																		# Unicode characters and puts them in the chars array; Cookbook 1.5.
			my @chars = unpack("C*", $formUni);							# Cookbook 1.5. In Perl 5.8.1 funktioniert split nicht wie gewünscht 
																		# mit Unicode-Zeichen.
			for my $char (@chars) {
				next unless ($char);									# Skip the rest of the block unless the value stored in the char variable 
																		# is a true value, i.e. not an empty string; Cookbook 1.0.
#				my $betaChar = $uniToBeta{$char};
#				$form .= $betaChar if ($betaChar);						# Cookbook 1.0.
				if ($char eq "206" or $char eq "207") {
				
					$gatekeeper = "off";
					next;
					
				}
				
				if ($gatekeeper eq "off") {
	
					my $betaChar = $asciiToBeta{$char};
					$form .= $betaChar if ($betaChar);					# Cookbook 1.0.
					$gatekeeper = "on";
					
				}
			}
			push (@forms, $form);
			$form = "";
		}

		my @cognatesUni = split " ", $cognateString;					# Camel3 29.2.161.
	
		foreach my $cognateUni (@cognatesUni) {

#			my @chars = split (/(&#\w+?;)/, $cognateUni);				# Splits up the string stored in the cognateUni variable into individual  
#																		# Unicode characters and puts them in the chars array; Cookbook 1.5.
			my @chars = unpack("C*", $cognateUni);							# Cookbook 1.5. In Perl 5.8.1 funktioniert split nicht wie gewünscht 
																		# mit Unicode-Zeichen.
			for my $char (@chars) {
				next unless ($char);									# Skip the rest of the block unless the value stored in the char variable 
																		# is a true value, i.e. not an empty string; Cookbook 1.0.
#				my $betaChar = $uniToBeta{$char};
#				$cognate .= $betaChar if ($betaChar);					# Cookbook 1.0.
				if ($char eq "206" or $char eq "207") {
				
					$gatekeeper = "off";
					next;
					
				}
				
				if ($gatekeeper eq "off") {
	
					my $betaChar = $asciiToBeta{$char};
					$cognate .= $betaChar if ($betaChar);				# Cookbook 1.0.
					$gatekeeper = "on";
					
				}
			}
			push (@cognates, $cognate);
			$cognate = "";
		}

	} elsif ($en eq "Beta") {
	
		$word = uc($wordIn);											# Converts the string stored in the wordIn variable to lowercase and 
																		# stores it in the word variable; Cookbook 1.9.
		$word =~ s/[^A-Z]//g;											# Removes from the content of the word variable all characters except
																		# for A-Z; Camel3 5.4.1.
		@forms = split " ", $formString;								# Camel3 29.2.161.
	
		foreach my $form (@forms) {

			$form = uc($form);											# Converts the string stored in the form variable to lowercase and 
																		# stores it back in the form variable; Cookbook 1.9.
			$form =~ s/[^A-Z]//g;										# Removes from the content of the form variable all characters except
																		# for A-Z; Camel3 5.4.1.
		}

		@cognates = split " ", $cognateString;							# Camel3 29.2.161.
	
		foreach my $cognate (@cognates) {

			$cognate = uc($cognate);									# Converts the string stored in the cognate variable to lowercase and 
																		# stores it back in the cognate variable; Cookbook 1.9.
			$cognate =~ s/[^A-Z]//g;									# Removes from the content of the cognate variable all characters except
																		# for A-Z; Camel3 5.4.1.
		}
	
	}																	# Closes the if ($en eq "Roman") block; Nutshell 4.3.

	if ($word eq "") {

		$message = "QuotationFinder has not received a Search Text word.";

		if ($en eq "Uni") {
			$message .= "<br>If you entered a word by clicking on the Greek letters,"
					 .	"<br>your browser is not compatible with Unicode input."
					 .	"<br>Please use Beta Code instead.";
		}

		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);					# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;

	}
	
	foreach my $loopKey ( keys %refText ) {

		if ($refText{$loopKey}{'Word'} eq $word and $refText{$loopKey}{'PosWordRef'} == $posWordRef and $q->param( "storeRefWordSubmit" )) {

			$word = convert_string_to_unicode($word) unless ($en eq "Roman");

			$message = "The word $word at position $posWordRef is already stored in this Search Text.";	# Stores a message in the variable named message;
																			# Camel3 1.5.3.
			print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																			# parentheses; Camel3 6.2, 6.2.3.
			exit;															# Aborts the current subroutine; Camel3 29.2.35.
		}
	}
	

	$refText{$key} = {													# Adds a new entry to the multidimensional refText hash, with $key as 
		'PosWordRef'	=>	$posWordRef,									# the key and two strings ($genFreq, $word) and two arrays (@forms, 
		'GenFreq'		=>	$genFreq,									# the key and two strings ($genFreq, $word) and two arrays (@forms, 
		'Word'			=>	$word,										# @cognates) as values; Cookbook 5.1, Camel 4.7.5.1, Camel3 2.9, 9.6.
		'Forms'			=>	[ @forms ],
		'Cognates'		=>	[ @cognates ],
	};
	
	untie %refText;														# Closes $mldbRefFile; Cookbook 14.1, CGI 10.2 (241).
	untie %refTextNames;												# Closes $mldbSearchFile; Cookbook 14.1, CGI 10.2 (241).

}																		# Closes the store_record subroutine; Camel3 6.2, Cookbook 10.0.


sub print_add_page{										# Begins the print_add_page subroutine. This subroutine is the
															# input screen a user sees when they want to add a new record. 
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1,
																		# CGI 11.2 (277).
	# The following JavaScript code checks to see if one word (no less, no more) has been entered in the 'Words' field, and that no non-
	# digits were entered in the 'Position' and 'Frequency' fields; Flanagan 5.10.7 (78), 6.4 (83), 6.9 (89), 9.1.1 (139), 9.2.7 (145)
	
	my $javaScript=<<END;

		function validateAddAWord()
		{
			var word = this.document.addAWord.Word.value;
			var chunks = word.split(/\\s+/);
			var patternW = /\\S/;
			var words = new Array();
			var i = 0;
			for (i in chunks) {
				if (patternW.test(chunks[i]) == 1) {
					words.push(chunks[i]);
				}
			}
			var posWordRef = this.document.addAWord.PosWordRef.value;
			var genFreq = this.document.addAWord.GenFreq.value;
			var patternD = /\\D/;
			if (words.length < 1) {
				alert("Please enter a word in the 'Word' field.");
				return false;
			}
			else if (words.length > 1) {
				alert("The 'Word' field cannot contain more than one word. Use the Forms and Cognates fields instead, or use the Add a Word function repeatedly to create a separate entry for every word.");
				return false;
			}
			if (patternD.test(posWordRef) == 1) {
				alert("The 'Position' field can only contain a number (integer). Simply number the words in your Search Text up to the position where the added word occurs, or leave the field blank.");
				return false;
			}
			if (patternD.test(genFreq) == 1) {
				alert("The 'Frequency' field can only contain a number (integer). This is for you to indicate how many times the word occurs in the CD-ROM you are about to search. You may leave the field blank.");
				return false;
			}
		}
END
#//			word.replace(/^\\s+(.*)/, "$1");							// Removes leading and trailing whitespace.
#//			word.replace(/(.*)\\s+$/, "$1");							// but doesn't work with Opera 6.0.3 for Mac OS X.
#//			alert("word is " + word);
#//			return false;
#//			var patternspace = /^\\s*\\S+\\s+\\S+\\s*$/;				// Doesn't work with Opera 6.0.3 for Mac OS X.
#//			var patternspace = /\\s*.+\\s+.+\\s*/;
#//			if (patternspace.test(word) == 1) {

	# The following JavaScript function makes the result of a clicked link appear in the addRefText HTML textarea.
	# It was inspired by http://www.thrall.org/proteus-virtualkb.html.
	if ($en eq "Uni") {

		$javaScript .= <<END;

			function virtualKeyboardWord(abcdef)
			{
				this.document.addAWord.Word.value+=abcdef
			}
			function virtualKeyboardForms(abcdef)
			{
				this.document.addAWord.Forms.value+=abcdef
			}
			function virtualKeyboardCognates(abcdef)
			{
				this.document.addAWord.Cognates.value+=abcdef
			}
END
	}


	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Add a Word',										# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-script=>$javaScript,
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form(
			-name=>'addAWord',
			-onSubmit=>"return validateAddAWord(this)",
		);

	
															# The following block of code
															# -	Begins a here document. A here document simply prints out
															# 	text until it encounters the terminator that you specify. The
															# 	terminator must be flush to the left side of the program and be on
															# 	the line by itself. Why it was named a here document escapes me. To
															# 	me the name is confusing. I would have called it a print block. 
															# -	Simply prints out HTML for the Add a Word screen.
															# -	Terminates the here document. 
	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );													# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
  
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>Add a Word</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Add_Word" target="Help">Help&nbsp;</a></td>
    <td class=roman>
HTML
      
	my $class;
	
	if ($en eq "Uni") {
		$class = "greek";
		print <<HTML;
      Fill in Greek words by clicking on the Greek letters under the appropriate text area. 
      <br>Remove, cut, copy, and paste text by clicking in the text area and using your mouse and keyboard.
      <p>Confirm by clicking on the Store this Word button.
HTML
	} elsif ($en eq "Beta") {
		$class = "roman";	# !
		print <<HTML;
      Fill in Greek words in <a href='http://www.tlg.uci.edu/BetaCode.html' target='_blank'>Beta Code</a> and click the Store this Word button.
HTML
	} else {
		$class = "roman";
		print <<HTML;
      Fill in these fields and click the Store this Word button.
HTML
	}

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right">Word:</td>
    <td class=$class> 
      <input type="text" name="Word" size="30">
    </td>
  </tr>
HTML

	if ($en eq "Uni") {
		print <<HTML;
  <tr>
    <td>&nbsp;</td>
    <td>
      <table>
        <tr>
HTML
		my @greekAlphabet = ("B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF", "C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9");
		foreach my $char (@greekAlphabet) {
			print "<td class=greek><a href=\"javascript:virtualKeyboardWord('&#x03$char;')\">&#x03$char;</a></td>";
		}
		print "<td class=greek><a href=\"javascript:virtualKeyboardWord(' ')\">[space]</a></td>";
	
		print <<HTML;
        </tr>
      </table>
    </td>
  </tr>
HTML
	}

	print <<HTML;
  <tr> 
    <td class=roman align="right">Position:</td>
    <td class=roman> 
      <input type="text" name="PosWordRef" size="15">
    </td>
  </tr>
  <tr> 
    <td class=roman align="right">Frequency:</td>
    <td class=roman> 
      <input type="text" name="GenFreq" size="15">
    </td>
  </tr>
  <tr> 
    <td class=roman align="right" valign="top">Forms:</td>
    <td class=$class> 
      <textarea name="Forms" cols="75" rows="3"></textarea>
    </td>
  </tr>
HTML

	if ($en eq "Uni") {
		print <<HTML;
  <tr>
    <td>&nbsp;</td>
    <td>
      <table>
        <tr>
HTML
		my @greekAlphabet = ("B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF", "C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9");
		foreach my $char (@greekAlphabet) {
			print "<td class=greek><a href=\"javascript:virtualKeyboardForms('&#x03$char;')\">&#x03$char;</a></td>";
		}
		print "<td class=greek><a href=\"javascript:virtualKeyboardForms(' ')\">[space]</a></td>";
	
		print <<HTML;
        </tr>
      </table>
    </td>
  </tr>
HTML
	}

	print <<HTML;
  <tr> 
    <td class=roman align="right" valign="top">Cognates:</td>
    <td class=$class> 
      <textarea name="Cognates" cols="75" rows="5"></textarea>
    </td>
  </tr>
HTML

	if ($en eq "Uni") {
		print <<HTML;
  <tr>
    <td>&nbsp;</td>
    <td>
      <table>
        <tr>
HTML
		my @greekAlphabet = ("B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF", "C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9");
		foreach my $char (@greekAlphabet) {
			print "<td class=greek><a href=\"javascript:virtualKeyboardCognates('&#x03$char;')\">&#x03$char;</a></td>";
		}
		print "<td class=greek><a href=\"javascript:virtualKeyboardCognates(' ')\">[space]</a></td>";
	
		print <<HTML;
        </tr>
      </table>
    </td>
  </tr>
HTML
	}

	my ($whDefault, $ptDefault);
	
	if ($mt eq "wh") {
	
		$whDefault = "'wh' checked";
		$ptDefault = "'pt'";
		
	} else {
	
		$whDefault = "'wh'";
		$ptDefault = "'pt' checked";
	
	}
	
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Confirm whether your Forms and Cognates fields contain
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value=$whDefault></td>
    <td class=roman>
HTML

	if ($en eq "Roman") {

		print <<HTML;
      whole words (e.g. "deposuit"&#151;will match only this form of "deponere"; faster option), or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value=$ptDefault></td>
    <td class=roman>
      parts of words (e.g. "depo"&#151;will match "depono," "deposuit," etc.)
HTML

	} else {

		print <<HTML;
      whole words (e.g. 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x03B9;&#x03BB;&#x03B5;&#x03BD;</span>"&#151;will match only this form of
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B1;&#x03B9;&#x03C1;&#x1F73;&#x03C9;</span>"; faster option), or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value=$ptDefault></td>
    <td class=roman>
      parts of words (e.g. 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x03B9;&#x03BB;</span>"&#151;will match 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x1FD6;&#x03BB;&#x03B5;</span>", 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x1FD6;&#x03BB;&#x03B5;&#x03BD;</span>", etc.)
HTML
	}

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="storeRefWordSubmit" value="Store this Word">
    </td>
  </tr>
</table>
HTML

	print	$q->hidden(													# We do not pass on a hidden value for "mt" this time.
				-name     => "id",										# There is a CGI parameter for mt being passed on from the 
				-default  => $id,										# form above.
			),															# CGI 11.2 (278)
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
}																		# Closes the print_add_page subroutine; Camel3 6.2, Cookbook 10.0.


sub delete_refTextWords{														# Begins the delete_refTextWords subroutine; Camel3 6.2, Cookbook 10.0. This
																		# subroutine performs user-selected deletions of entries from the refe-
																		# rence text hashes.	
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1,
																		# CGI 11.2 (277).
	my $current;														# Declares a private variable that exists only within the innermost en-
																		# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	
	error( $q, "searchDir is an empty string, I'm in delete_refTextWords." ) if ($searchDir eq "");
	error( $q, "userDir is an empty string, mldbSearchFile is $mldbSearchFile, I'm in delete_refTextWords." ) if ($userDir eq "");	# For debugging
	my $mldb = tie %refText, 'MLDBM', $mldbRefFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbRefFile is $mldbRefFile $!" );
																		# Associates the database file whose path is stored in the mldbRefFile
																		# variable with the refText hash so that, using the MLDBM module, any
																		# changes to the hash are saved to the file (which is created with 
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), 10.2 (241), DBI 2.7 (32), 2.9 (51), 
																		# Cozens 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	foreach $key (keys %refText) {									# For each key in the refText hash, the following block of code is
																		# executed; Cookbook 5.4. 
		foreach $current (@keys) {										# For each value (stored in $current) of the keys array, the following
																		# block of code is executed; Cookbook 4.4. The keys array is the values
																		# of all of the checkboxes that were checked on the calling Web page.
			if ($current == $key) {										# If $current is equal to $key, the following block of code is execu-
																		# ted; Camel3 4.3, 1.5.6. We now have a match of a delete checkbox mark
																		# and a search text hash key.
				delete $refText{$key};									# Deletes the $key entry from the refText hash; Cookbook 5.3.
			}															# Closes the if block; Nutshell 4.3.
		}																# Closes the foreach loop that goes through @keys; Nutshell 4.3.
	} # End of foreach $current loop.									# Closes the foreach loop that goes through %refText; Nutshell 
																		# 4.3.
	untie %refText;														# Closes $mldbRefFile; Cookbook 14.1, CGI 10.2 (241).
}																		# Closes the delete_refTextWords subroutine; Camel3 6.2, Cookbook 10.0.


sub print_modify_page{													# Begins the print_modify_page subroutine; Camel3 6.2, Cookbook 10.0.
																		# This subroutine displays the page that contains the data for the one
																		# item the user selected for modification.
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1,
																		# CGI 11.2 (277).
	my ($posWordRef, $genFreq, $wordDisp, @formsDisp, @cognatesDisp);
	
	# The following JavaScript code checks to see if one word (no less, no more) has been entered in the 'Words' field, and that no non-
	# digits were entered in the 'Position' and 'Frequency' fields; Flanagan 5.10.7 (78), 6.4 (83), 6.9 (89), 9.1.1 (139), 9.2.7 (145)

	my $javaScript=<<END;

		function validateModifyWord()
		{
			var word = this.document.modifyWord.Word.value;
			var chunks = word.split(/\\s+/);
			var patternW = /\\S/;
			var words = new Array();
			var i = 0;
			for (i in chunks) {
				if (patternW.test(chunks[i]) == 1) {
					words.push(chunks[i]);
				}
			}
			var posWordRef = this.document.modifyWord.PosWordRef.value;
			var genFreq = this.document.modifyWord.GenFreq.value;
			var patternD = /\\D/;
			if (words.length < 1) {
				alert("Please enter a word in the 'Word' field.");
				return false;
			}
			else if (words.length > 1) {
				alert("The 'Word' field cannot contain more than one word. Use the Forms and Cognates fields instead, or use the Add a Word function repeatedly to create a separate entry for every word.");
				return false;
			}
			if (patternD.test(posWordRef) == 1) {
				alert("The 'Position' field can only contain a number (integer). Simply number the words in your Search Text up to the position where the added word occurs, or leave the field blank.");
				return false;
			}
			if (patternD.test(genFreq) == 1) {
				alert("The 'Frequency' field can only contain a number (integer). This is for you to indicate how many times the word occurs in the CD-ROM you are about to search. You may leave the field blank.");
				return false;
			}
		}
END
	
	# The following JavaScript function makes the result of a clicked link appear in the addRefText HTML textarea.
	# It was inspired by http://www.thrall.org/proteus-virtualkb.html.

	if ($en eq "Uni") {

		$javaScript .= <<END;

			function virtualKeyboardWord(abcdef)
			{
				this.document.modifyWord.Word.value+=abcdef
			}
			function virtualKeyboardForms(abcdef)
			{
				this.document.modifyWord.Forms.value+=abcdef
			}
			function virtualKeyboardCognates(abcdef)
			{
				this.document.modifyWord.Cognates.value+=abcdef
			}
END
	}

	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Modify Word',									# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-script=>$javaScript,
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form(
			-name=>'modifyWord',
			-onSubmit=>"return validateModifyWord(this)",
		);

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );													# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
  
	my $key = $keys[0];													# Gets the first element stored in the keys array(!) and stores it in 
																		# the key variable; Learning 3.4.2.
															# The first record is the record
															# we want to modify. It should also be the only record in the array.
															# We store the first item split out in the $key variable. The rest of the
															# fields in the database go into the array @field_vals. 
	
	error( $q, "userDir is an empty string, I'm in print_modify_page." ) if ($userDir eq "");
	error( $q, "searchDir is an empty string, I'm in print_modify_page." ) if ($searchDir eq "");
	my $mldb = tie %refText, 'MLDBM', $mldbRefFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbRefFile is $mldbRefFile $!" );
																		# Associates the database file whose path is stored in the mldbRefFile
																		# variable with the refText hash so that, using the MLDBM module, any
																		# changes to the hash are saved to the file (which is created with 
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), 10.2 (241), DBI 2.7 (32), 2.9 (51), 
																		# Cozens 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.


	$posWordRef	= $refText{$key}{'PosWordRef'};
	$genFreq	= $refText{$key}{'GenFreq'};

	if ($en eq "Uni") {
		$chunk			= $refText{$key}{'Word'};
		$wordDisp		= convert_refTextChunk_to_unicode($chunk);	# Cookbook 4.4.
		@formsDisp		= @{ $refText{$key}{'Forms'} };
		foreach $chunk (@formsDisp) {
			$chunk		= convert_refTextChunk_to_unicode($chunk);	# Cookbook 4.4.
		}
		@cognatesDisp	= @{ $refText{$key}{'Cognates'} };
		foreach $chunk (@cognatesDisp) {
			$chunk		= convert_refTextChunk_to_unicode($chunk);	# Cookbook 4.4.
		}
	} else {
		$wordDisp		= $refText{$key}{'Word'};
		@formsDisp		= @{ $refText{$key}{'Forms'} };
		@cognatesDisp	= @{ $refText{$key}{'Cognates'} };
	}
															# The next block of code is a here document containing the HTML for the top part
															# of the Modify Word screen. We store the $key in a hidden form
															# element so we can keep track of the record we are modifying. 
	print <<HTML;
  <input type=hidden name=key value="$key">
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td> 
      <h5>Modify Word</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Fill_Fields" target="Help">Help&nbsp;</a></td>
    <td class=roman>
HTML
      
	if ($en eq "Uni") {
		print <<HTML;
      Add Greek letters at the end of the text by clicking on the Greek letters under the appropriate text area. 
      <br>Remove, cut, copy, and paste text by clicking in the text area and using your mouse and keyboard.
      <p>Confirm by clicking on the Store this Word button.
HTML
	} else {
		print <<HTML;
      Modify these fields and click the Store this Word button.
HTML
	}

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr>
    <td class=roman align="right" valign="bottom">Word:</td>
    <td> 
      <input type="text" name="Word" size="30" value="$wordDisp">
    </td>
  </tr>
HTML

	if ($en eq "Uni") {
		print <<HTML;
  <tr>
    <td>&nbsp;</td>
    <td>
      <table>
        <tr>
HTML
		my @greekAlphabet = ("B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF", "C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9");
		foreach my $char (@greekAlphabet) {
			print "<td class=greek><a href=\"javascript:virtualKeyboardWord('&#x03$char;')\">&#x03$char;</a></td>";
		}
		print "<td class=greek><a href=\"javascript:virtualKeyboardWord(' ')\">[space]</a></td>";
	
		print <<HTML;
        </tr>
      </table>
    </td>
  </tr>
HTML
	}

	print <<HTML;
  <tr>
    <td class=roman align="right">Position:</td>
    <td class=roman> 
      <input type="text" name="PosWordRef" size="15" value="$posWordRef">
    </td>
  </tr>
  <tr>
    <td class=roman align="right">Frequency:</td>
    <td class=roman> 
      <input type="text" name="GenFreq" size="15" value="$genFreq">
    </td>
  </tr>
  <tr>
    <td class=roman align="right" valign="top">Forms:</td>
    <td> 
      <textarea name="Forms" cols="75" rows="3">@formsDisp</textarea>
    </td>
  </tr>
HTML

	if ($en eq "Uni") {
		print <<HTML;
  <tr>
    <td>&nbsp;</td>
    <td>
      <table>
        <tr>
HTML
		my @greekAlphabet = ("B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF", "C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9");
		foreach my $char (@greekAlphabet) {
			print "<td class=greek><a href=\"javascript:virtualKeyboardForms('&#x03$char;')\">&#x03$char;</a></td>";
		}
		print "<td class=greek><a href=\"javascript:virtualKeyboardForms(' ')\">[space]</a></td>";
	
		print <<HTML;
        </tr>
      </table>
    </td>
  </tr>
HTML
	}

	print <<HTML;
  <tr>
    <td class=roman align="right" valign="top">Cognates:</td>
    <td> 
      <textarea name="Cognates" cols="75" rows="5">@cognatesDisp</textarea>
    </td>
  </tr>
HTML

	if ($en eq "Uni") {
		print <<HTML;
  <tr>
    <td>&nbsp;</td>
    <td>
      <table>
        <tr>
HTML
		my @greekAlphabet = ("B1", "B2", "B3", "B4", "B5", "B6", "B7", "B8", "B9", "BA", "BB", "BC", "BD", "BE", "BF", "C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9");
		foreach my $char (@greekAlphabet) {
			print "<td class=greek><a href=\"javascript:virtualKeyboardCognates('&#x03$char;')\">&#x03$char;</a></td>";
		}
		print "<td class=greek><a href=\"javascript:virtualKeyboardCognates(' ')\">[space]</a></td>";
	
		print <<HTML;
        </tr>
      </table>
    </td>
  </tr>
HTML
	}

	my ($whDefault, $ptDefault);
	
	if ($mt eq "wh") {
	
		$whDefault = "'wh' checked";
		$ptDefault = "'pt'";
		
	} else {
	
		$whDefault = "'wh'";
		$ptDefault = "'pt' checked";
	
	}
	
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Confirm whether your Forms and Cognates fields contain
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value=$whDefault></td>
    <td class=roman>
HTML

	if ($en eq "Roman") {

		print <<HTML;
      whole words (e.g. "deposuit"&#151;will match only this form of "deponere"; faster option), or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value=$ptDefault></td>
    <td class=roman>
      parts of words (e.g. "depo"&#151;will match "depono," "deposuit," etc.)
HTML

	} else {

		print <<HTML;
      whole words (e.g. 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x03B9;&#x03BB;&#x03B5;&#x03BD;</span>"&#151;will match only this form of
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B1;&#x03B9;&#x03C1;&#x1F73;&#x03C9;</span>"; faster option), or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='mt' value=$ptDefault></td>
    <td class=roman>
      parts of words (e.g. 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x03B9;&#x03BB;</span>"&#151;will match 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x1FD6;&#x03BB;&#x03B5;</span>", 
      "<span class=greek>&#x03BA;&#x03B1;&#x03B8;&#x03B5;&#x1FD6;&#x03BB;&#x03B5;&#x03BD;</span>", etc.)
HTML
	}

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="storeModifiedRefWordSubmit" value="Store this Word">
    </td>
  </tr>
</table>
HTML

	untie %refText;														# Closes $mldbRefFile; Cookbook 14.1, CGI 10.2 (241).

	print	$q->hidden(													# We do not pass on a hidden value for "mt" this time.
				-name     => "id",										# There is a CGI parameter for mt being passed on from the 
				-default  => $id,										# form above.
			),															# CGI 11.2 (278)
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
}																		# Closes the print_modify_page subroutine; Camel3 6.2, Cookbook 10.0.


sub multiple_match{														# Begins the multiple_match subroutine; Camel3 6.2, Cookbook 10.0. This
																		# subroutine displays the search text database if it contains more than
																		# one record.
	my ( $wordCount, $caption, $buttonText, $q, $id, $mo, $se, $en, $mt, $su ) = @_;					# Copies the 9 first values passed to the subroutine, contained in the @_ ar-
																		# ray, to the count, caption, buttonText, q, id and se private variables, 
																		# respectively; Camel3 6.2.1, CGI 11.2 (277).

	my $name = $_[11] || "viewNavigation";
	
	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Search Text Words',									# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form;

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );													# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
  
															# The next block of code is a here document that prints out the page heading
															# information for the Multiple Match screen. Notice on line 210 we use

	error( $q, "userDir is an empty string, I'm in sub multiple_match." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub multiple_match." ) if ($searchDir eq "");
	my $mldb = tie %refText, 'MLDBM', $mldbRefFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbRefFile is $mldbRefFile $!" );
																		# Associates the database file whose path is stored in the mldbRefFile
																		# variable with the refText hash so that, using the MLDBM module, any
																		# changes to the hash are saved to the file (which is created with 
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), 10.2 (241), DBI 2.7 (32), 2.9 (51), 
																		# Cozens 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	my ($posWordRef, $genFreq);									# Declares private variables that exist only within the innermost en-
	my @sortedKeysRef;								# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	
#	@sortedKeysRef = sort { $posRefLookup{$a} <=> $posRefLookup{$b} } keys %posRefLookup;
															# Cookbook 5.9;
	# The above sort function was replaced by the one following as we need to sort refText entries not just based on the position of the word 
	# in the search text, but also alphabetically when users have entered more than one word per position using the Add function. The ordering
	# is necessary because otherwise there would be no way of telling which entries would get displayed on any given page produced by the cur-
	# rent subroutine, making it tricky, confusing, and irritating to view, modify, or delete words added later.
	my (%posWordRefs, %words);
	for my $key ( keys %refText ) {					# Camel3 9.2.3.
		$words{$key} = $refText{$key}{'Word'};
		$posWordRefs{$key} = $refText{$key}{'PosWordRef'};
	}
	@sortedKeysRef = sort { $posWordRefs{$a} <=> $posWordRefs{$b} or $words{$a} cmp $words{$b} } keys %posWordRefs;	# Sorts on position, and, 
																		# if the position is the same, on words; Cookbook 5.9, Hall/Schwartz 
																		# §14 (54)
#	@sortedKeysRef = sort { $refText{$key}{'PosWordRef'}{$a} <=> $refText{$key}{'PosWordRef'}{$b} or $refText{$key}{'Word'}{$a} cmp $refText{$key}{'Word'}{$b} } keys %refText;	# Sorts on position, and, 
																		# if the position is the same, on words; Cookbook 5.9, Hall/Schwartz 
																		# §14 (54)

	
#DIE FOLGENDE TECHNIK STAMMT AUS DEM FILE dbAnnotated.cgi AUS DEM DBMan ORDNER. 
#INDEM IN DEN LINK EIN ACTION-ATTRIBUT EINGEBAUT WIRD,
#KANN DAS ERNEUTE DURCHSUCHEN DER GROSSEN FILES üBERSPRUNGEN WERDEN; VGL. CGI PROGRAMMING S. 275, PERL AND CGI S. 57. DAMIT DIES ABER FUNK-
#TIONIERT, MUSS DIE DB_File FEHLERMELDUNG VERSCHWINDEN, DAMIT DAS SCRIPT NICHT AM ENDE DER %score-SUBROUTINE SCHON ABSCHMIERT...
#DIE DB_File FEHLERMELDUNG ***IST*** VERSCHWUNDEN IN APACHE / MAC OS X!!!!!!!

	my ($nextPage, $prevPage, $left, $right, $lower, $upper, $pageLinks, $i, $first, $last, $lastPage);
	my $numRecs = @sortedKeysRef;										# Declares private variables that exist only within the innermost en-
																		# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	
	my $maxRecs = 5;													# Stores the value 5 in the maxRecs variable; Learning 2.6. We will use
																		# this to determine the maximum number of records displayed per page.

	# If we have more records than we want to display on one page, we build a pagelink toolbar for navigating the pages.
	if ($numRecs > $maxRecs) {											# If the value stored in the numRecs variable is greater than the one
																		# stored in the maxRecs variable, the following block of code is 
																		# executed; Learning 2.4.2, Camel 2.5.11. We only want to build the
																		# toolbar if we have more records than we want to display on one page.
		$nextPage = $page + 1;											# Increases/diminishes the page variable by 1 and stores the results
		$prevPage = $page - 1;											# in the nextPage/prevPage variable; Learning 2.4.1. This will be used 
																		# for the [Next]/[Previous] links in the toolbar.
		$lastPage = $numRecs / $maxRecs;								# Divides the value stored in the numRecs variable by the one stored in
																		# the maxRecs variable; Learning 2.4.1.
		$lastPage = int $lastPage + 1 unless ($lastPage == int $lastPage);	# Takes the integer portion of the value stored in the lastPage
																		# variable, adds one, and replaces the value previously stored in the
																		# lastPage variable with the results unless the old lastPage value is 
																		# equal to the integer portion of the same; Camel 3.2.76. This   
																		# operation rounds up the results of the division above in case it isn't
																		# an integer.
																		# THE SAME EFFECT COULD BE HAD BY USING THE ceil() FUNCTION OF THE 
																		# POSIX MODULE, BUT I GUESS IT'S NOT WORTH THE OVERHEAD; Cookbook 2.3.

		# We now calculate how many pages we have to the left and the right of the current page.
		$left  = $page - 1;												# Subtracts 1 from the value stored in the page variable and stores the
																		# results in the variable called left; Learning 2.6. This is how many 
																		# pages we have to the left of the current page.
		$right = $lastPage - $page;										# Subtracts the value stored in the page variable from the one stored 
																		# in the lastPage variable, and stores the results in the variable 
																		# called right; Learning 2.4.1. This is how many pages we have to the
																		# right of the current page.

		# In case we have so many pages that we can't list links to every one of them in the toolbar, we need a lower and upper limit for the
		# page links we are going display to the left and the right of the current page, with special provisions for when we are near the first
		# or the last page.
		if ($right < 7) {												# If the value stored in the variable called right is less than 7, the
																		# following block of code is executed; Learning 2.4.2, Camel 2.5.11. 
			$lower = $lastPage - 14;									# Subtracts 14 from the value stored in the lastPage variable and puts 
																		# the results in the lower variable; Learning 2.4.1. If we are on one of
																		# the last 7 pages, we will display the whole right end of the page  
																		# link spectrum.
		} else {														# If the condition above is not met, the following block of code is
																		# executed; Learning 4.2.
			$lower = $page - 7;											# Takes the value stored in the page variable, subtracts 7 from it, and
																		# stores the results in the lower variable; Learning 2.4.1. This will be
																		# the lower limit for page number links in the toolbar if we have more 
																		# than 7 pages on the left.
																		# We don't need to worry about values for $lower that are less than 1,
																		# as they will automatically be ignored by the for loop below.
		}																# Closes the if ... else block; Learning 4.1.
		if ($left < 7) {												# If the value stored in the variable called left is less than 7, the
																		# following block of code is executed; Learning 2.4.2, Camel 2.5.11. 
			$upper = 15;												# Assigns the value of 15 to the variable called upper; Learning 2.6. 
																		# If we are on one of the first 7 pages, we will display the whole left 
																		# end of the page link spectrum.
		} else {														# If the condition above is not met, the following block of code is
																		# executed; Learning 4.2.
			$upper = $page + 7											# Takes the value stored in the page variable, adds 7 to it, and stores
																		# the results in the upper variable; Learning 2.4.1. This will be the
																		# upper limit for page number links in the toolbar if we have more than
																		# 7 pages on the right.
																		# We don't need to worry about values for $upper that are greater than
																		# $lastPage, as they will automatically be ignored by the for loop
																		# below.
		}																# Closes the if ... else block; Learning 4.1.

#		$pageLinks = "";

		# Now we build the HTML toolbar by appending piece by piece to the pageLinks variable.
		($lower > 1)	and ($pageLinks .= qq~<a href="$qfUrl?action=$action&page=1&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[First]</a> ~);
																		# Checks to see if the parenthesis to the left of "and" is true, i.e.
																		# if the value stored in the variable called lower is greater than 1, 
																		# and, if so, executes the parenthesis to the right of "and," i.e. 
																		# appends the HTML link to page 1 to the string stored in the pageLinks 
																		# variable; Learning 2.6.1, Camel 2.5.14, 2.5.20, 8.4, Cookbook 1.0, 
																		# 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl and CGI 56.
		($page > 1)		and ($pageLinks .= qq~<a href="$qfUrl?action=$action&page=$prevPage&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[Previous]</a> ~);
																		# Checks to see if the parenthesis to the left of "and" is true, i.e.
																		# if the value stored in the variable called page is greater than 1, 
																		# and, if so, executes the parenthesis to the right of "and," i.e. 
																		# appends the HTML link to the previous page to the string stored in  
																		# the pageLinks variable; Learning 2.6.1, Camel 2.5.14, 2.5.20, 8.4, 
																		# Cookbook 1.0, 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl 
																		# and CGI 56.
		for ($i = 1; $i <= $lastPage; $i++) {							# Sets the initial value of the counter variable i to 1, determines 
																		# that this will go on as long as the counter is less than or equal to 
																		# the value stored in the lastPage variable, sets the auto-increment
																		# operator in motion, and executes the following block for every value
																		# of i that meets the condition; Learning 4.4.
			if ($i < $lower) {											# If the value of the i counter is less than that of the variable 
																		# called lower, the following block of code is executed; Learning 
																		# 2.4.2.
				$pageLinks .= " ... " if ($lower > 2);					# Appends ellipsis points to the pageLinks variable if the value stored
																		# in the lower variable is greater than 2; Learning 2.4.2.
				$i = ($lower - 1);										# Subtracts 1 from the value stored in the lower variable and puts the
																		# results in the i counter; Learning 2.4.1. We can skip all values of i
																		# until we are just below $lower, because we won't display them in the 
																		# pagelinks toolbar.
				next;													# Causes execution to skip past the rest of the for block without
																		# terminating the block; Learning 9.2.
			} elsif ($i > $upper) {										# If the value of the i counter is greater than that of the variable 
																		# called upper, the following block of code is executed; Learning 
																		# 2.4.2.
				$pageLinks .= " ... " if ($lastPage - $upper > 1);		# Appends ellipsis points to the pageLinks variable if the difference  
																		# between the values stored in the lastPage and upper variables is 
																		# greater than 1; Learning 2.4.2.
				last;													# Causes execution to break out of the for block and to continue with
																		# the statement immediately following the block; Learning 9.1.
			} elsif ($i == $page) {										# If the value of the counter i is equal to the value stored in the
																		# page variable, the following block of code is executed; Learning 
																		# 2.4.2.
				$pageLinks .= qq~$i ~;									# Appends the current value of the i counter to the pageLinks variable;
																		# Cookbook 1.0, 4.1. We don't need to provide a link to the current 
																		# page, since we are on it.
			} else {													# If none of the conditions above are met, the following block of code
																		# is executed; Learning 4.2.
				$pageLinks .= qq~<a href="$qfUrl?action=$action&page=$i&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">$i</a> ~;
																		# Appends the HTML link to the page indicated by the current value of i
																		# to the string stored in the pageLinks variable unless the current
																		# value of the page variable is equal to the one of the lastPage
																		# variable; Learning 2.6.1, Cookbook 1.0, 4.1, HTML Definitive 7.3.3
																		# (219f), CGI 101 111f, Perl and CGI 56.
			}															# Closes the if ... elsif ... else block; Learning 4.1.
		}																# Closes the for block; Learning 4.1.
		$pageLinks .= qq~<a href="$qfUrl?action=$action&page=$nextPage&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[Next]</a> ~ unless ($page == $lastPage);
																		# Appends the HTML link to the next page to the string stored in the 
																		# pageLinks variable unless the current value of the page variable is
																		# equal to the one of the lastPage variable; Learning 2.6.1, Cookbook 
																		# 1.0, 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl and CGI 
																		# 56. We don't want to provide a link to the next page if we are on the
																		# last one.
		$pageLinks .= qq~<a href="$qfUrl?action=$action&page=$lastPage&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[Last]</a> ~ if ($lastPage > $upper);
																		# Appends the HTML link to the last page to the string stored in the 
																		# pageLinks variable if the value stored in the lastPage variable is
																		# greater than the one in the upper variable; Learning 2.6.1, Cookbook 
																		# 1.0, 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl and CGI 
																		# 56. We only provide a [Last] link if there is no link to the last 
																		# page by page number.
		
# Slice the @sortedKeysRef to only return the ones we want, only have to do this if the results are sorted.					#ONLY THE HITS WE WANT
#		if (exists $in{'sb'}) {			
			$first = $maxRecs * ($page - 1);
			$last  = $first + $maxRecs - 1;		
			if ($last > $#sortedKeysRef) {
				$last = $#sortedKeysRef;
			}
			@sortedKeysRef = @sortedKeysRef[$first .. $last];
#		}
	}

															# the variable $caption that we set before this subroutine was called. 
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>$caption</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
HTML
	if (@_ > 10 and $_[11] =~ /modify/) {								# Checks to see if @_ contains more than 10 items and the 12th item 
																		# passed to the subroutine, $_[11], was modify--if so, we execute 
																		# the code inside of the block. 
		print <<HTML;
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Modify_Words" target="Help">Help&nbsp;</a></td>
HTML

	} 																	# Closes the if (@_ > 10) block; Nutshell 4.3.		
	elsif (@_ > 10 and $_[11] =~ /delete/) {								# Checks to see if @_ contains more than 10 items and the 12th item 
																		# passed to the subroutine, $_[11], was delete--if so, we execute 
																		# the code inside of the block. 
		print <<HTML;
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Delete_Words" target="Help">Help&nbsp;</a></td>
HTML

	} 																	# Closes the if (@_ > 10) block; Nutshell 4.3.
	else {	
		print <<HTML;
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#View_Words" target="Help">Help&nbsp;</a></td>
HTML

	}
	print <<HTML;
    <td class=roman>There are $wordCount words in this Search Text.</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	if ($pageLinks ne "") {
	
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>$pageLinks</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}

	foreach $key (@sortedKeysRef) {
		
		my ($class, $wordDisp, @formsDisp, $formDisp, $formsNumber, $formsPerColumn, @cognatesDisp, $cognateDisp, $cognatesNumber, $cognatesPerColumn, $iCols, $iForms, $iCognates);
																		# Declares private variables that exist only within the innermost en-
																		# closing block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
		$posWordRef		= $refText{$key}{'PosWordRef'};
		$genFreq		= $refText{$key}{'GenFreq'};

		if ($en eq "Roman") {
			$class			= "roman";
			$wordDisp		= $refText{$key}{'Word'};
			@formsDisp		= @{ $refText{$key}{'Forms'} }		if defined @{ $refText{$key}{'Forms'} };
			@cognatesDisp	= @{ $refText{$key}{'Cognates'} }	if defined @{ $refText{$key}{'Cognates'} };
		} else {
			$class			= "greek";
			$chunk			= $refText{$key}{'Word'};
			$wordDisp		= convert_refTextChunk_to_unicode($chunk);	# Cookbook 4.4.
			@formsDisp		= @{ $refText{$key}{'Forms'} };
			foreach $chunk (@formsDisp) {
				$chunk		= convert_refTextChunk_to_unicode($chunk);	# Cookbook 4.4.
			}
			@cognatesDisp	= @{ $refText{$key}{'Cognates'} };
			foreach $chunk (@cognatesDisp) {
				$chunk		= convert_refTextChunk_to_unicode($chunk);	# Cookbook 4.4.
			}
		}
		
		if (@_ > 10 and $_[11] =~ /(modify|delete)/) {					# Checks to see if @_ contains more than 10 items and the 12th item 
																		# passed to the subroutine, $_[11], was modify or delete--if so, we 
																		# execute the code inside of the block. 
															#
															# On this line, we specify input type=$_[5].... Remember that when we
															# called this subroutine, the first thing we passed it was RADIO or
															# CHECKBOX. This is what determines what type of HTML input field is

			print <<HTML;
  <tr> 
    <td class=roman align="right">Select:</td>
    <td> 
      <input type=$_[10] name=key value=$key>
    </td>
  </tr>
HTML

		} 																# Closes the if (@_ > 6) block; Nutshell 4.3.		
		print <<HTML;
  <tr> 
    <td class=roman align="right" valign="bottom">Word:</td>
    <td class=$class style="font-size: larger">$wordDisp</td>
  </tr>
  <tr> 
    <td class=roman align="right">Position:</td>
    <td class=roman>$posWordRef</td>
  </tr>
  <tr> 
    <td class=roman align="right">Frequency:</td>
    <td class=roman>$genFreq</td>
  </tr>
  <tr> 
    <td class=roman align="right" valign="bottom">Forms:</td>
    <td class=$class> 
      <table width="588" cellpadding="0" cellspacing="0" border="0">
        <tr valign="top"> 
          <td width="147">
HTML

		$formsNumber = @formsDisp;											# Counts the number of elements stored in the formsDisp array and puts the 
																		# results in the formsNumber variable; Nutshell 4.2.5, Camel 2.3.4.
		$formsPerColumn = $formsNumber / 4;								# Divides the formsNumber variable by 4 and puts the results in the  
																		# formsPerColumn variable; Learning 2.4.1.
		$formsPerColumn = int $formsPerColumn + 1 unless ($formsPerColumn == int $formsPerColumn);	# Takes the integer portion of the value 
																		# stored in the formsPerColumn variable, adds one, and replaces the 
																		# value previously stored in the formsPerColumn variable with the  
																		# results unless the old formsPerColumn value is equal to the integer 
																		# portion of the same; Camel 3.2.76. This operation rounds up the 
																		# results of the division by 4 above in case it isn't an integer. We do
																		# this because we don't want the first 3 columns to be shorter than the
																		# 4th.
																		# THE SAME EFFECT COULD BE HAD BY USING THE ceil() FUNCTION OF THE 
																		# POSIX MODULE, BUT I GUESS IT'S NOT WORTH THE OVERHEAD; Cookbook 2.3.
		$iCols = 1;														# Sets the variable iCols, which we will use as a counter, to 1;
																		# Learning 4.4.
		$iForms = 0;													# Sets the variable iForms, which we will use as a counter, to 0;
																		# Learning 4.4.
		foreach $formDisp (@formsDisp) {										# Takes each element of the formsDisp array and assigns them one at a time
																		# to the form variable, executing the following block of code with
																		# each successive assignment; Learning 4.5.
			if ($iForms == $formsPerColumn) {							# Checks to see if the value stored in the counter variable is equal to
																		# the value stored in the formsPerColumn variable--if so, we enter the
																		# following block of code; Learning 2.4.2, 4.2. Remember that the coun-
																		# ter starts at 0--by the time it is equal to $formsPerColumn, the 
																		# column is actually already full.
				print "</td>\n          <td width=147>";				# Prints two HTML tags: one that closes a table cell, and one that
																		# opens a new one; HTML 11.2.4 (384-390).
				$iCols++;												# Increments the value of the column counter variable; Learning 2.6.2.
				$iForms = 0;											# Resets the form counter variable to 0; Learning 4.4.
			}															# Closes the if ($iForms == $formsPerColumn) block; Learning 4.1.
			print "$formDisp<br>";											# Prints the current value of the form variable, then an HTML line 
																		# break; HTML 4.7.1 (94-98).
			$iForms++;													# Increments the value of the forms counter variable; Learning 2.6.2.
		}																# Closes the foreach $formDisp block; Learning 4.1.
		while ($iCols < 4) {											# Evaluates if the value stored in the column counter variable is less
																		# than 4--as long as this is so, the following block of code is exe-
																		# cuted repeatedly; Learning 4.3. We need to print HTML tags for all 4 
																		# columns in order to keep the columns aligned.
				print "</td>\n          <td width=147>";				# Prints two HTML tags: one that closes a table cell, and one that
																		# opens a new one; HTML 11.2.4 (384-390).
				$iCols++;												# Increments the value of the column counter variable; Learning 2.6.2.
		}																# Closes the while block; Nutshell 4.3.
		
		print <<HTML;
          </td>
        </tr>
      </table>
    </td>
  </tr>
  <tr> 
    <td class=roman align="right" valign="bottom">Cognates:</td>
    <td class=$class> 
      <table width="588" cellpadding="0" cellspacing="0" border="0">
        <tr valign="top"> 
          <td width="147">
HTML

		$cognatesNumber = @cognatesDisp;									# Counts the number of elements stored in the cognatesDisp array and puts 
																		# the results in the cognatesNumber variable; Nutshell 4.2.5.
		$cognatesPerColumn = $cognatesNumber / 4;						# Divides the cognatesNumber variable by 4 and puts the results in the 
																		# cognatesPerColumn variable; Learning 2.4.1.
		$cognatesPerColumn = int $cognatesPerColumn + 1 unless ($cognatesPerColumn == int $cognatesPerColumn);	# Takes the integer portion of 
																		# the value stored in the formsPerColumn variable, adds one, and  
																		# replaces the value previously stored in the formsPerColumn variable  
																		# with the results unless the old formsPerColumn value is equal to the  
																		# integer portion of the same; Camel 3.2.76. This operation rounds up  
																		# the results of the division by 4 above in case it isn't an integer. We
																		# do this because we don't want the first 3 columns to be shorter than 
																		# the 4th.
																		# THE SAME EFFECT COULD BE HAD BY USING THE ceil() FUNCTION OF THE 
																		# POSIX MODULE, BUT I GUESS IT'S NOT WORTH THE OVERHEAD; Cookbook 2.3.
		$iCols = 1;														# Sets the variable iCols, which we will use as a counter, to 1;
																		# Learning 4.4.
		$iCognates = 0;													# Sets the variable iCognates, which we will use as a counter, to 0; 
																		# Learning 4.4.
		foreach $cognateDisp (@cognatesDisp) {									# Takes each element of the cognatesDisp array and assigns them one at a
																		# time to the cognate variable, executing the following block of code
																		# with each successive assignment; Learning 4.5.
			if ($iCognates == $cognatesPerColumn) {						# Checks to see if the value stored in the counter variable is equal to
																		# the value stored in the cognatesPerColumn variable--if so, we enter
																		# the following block of code; Learning 2.4.2, 4.2. Remember that the 
																		# counter starts at 0--by the time it is equal to $cognatesPerColumn, 
																		# the column is actually already full.
				print "</td>\n          <td width=147>";				# Prints two HTML tags: one that closes a table cell, and one that
																		# opens a new one; HTML 11.2.4 (384-390).
				$iCols++;												# Increments the value of the column counter variable; Learning 2.6.2.
				$iCognates = 0;											# Resets the cognate counter variable to 0; Learning 4.4.
			}															# Closes the if ($iCognates == $cognatesPerColumn) block; Learning 4.1.
			print "$cognateDisp<br>";										# Prints the current value of the cognate variable, then an HTML line 
																		# break; HTML 4.7.1 (94-98).
			$iCognates++;												# Increments the value of the counter variable; Learning 2.6.2.
		}																# Closes the foreach $cognateDisp block; Learning 4.1.
		while ($iCols < 4) {											# Evaluates if the value stored in the column counter variable is less
																		# than 4--as long as this is so, the following block of code is exe-
																		# cuted repeatedly; Learning 4.3. We need to print HTML tags for all 4 
																		# columns in order to keep the columns aligned.
				print "</td>\n          <td width=147>";				# Prints two HTML tags: one that closes a table cell, and one that
																		# opens a new one; HTML 11.2.4 (384-390).
				$iCols++;												# Increments the value of the column counter variable; Learning 2.6.2.
		}																# Closes the while block; Nutshell 4.3.
		
		print <<HTML;
          </td>
        </tr>
      </table>
    </td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	}															# Ends foreach $key block.

	if ($pageLinks ne "") {
	
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>$pageLinks</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}

	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="$name" value="$buttonText">
    </td>
  </tr>
</table>
HTML

	untie %refText;														# Closes $mldbRefFile; Cookbook 14.1, CGI 10.2 (241).

	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "mt",
				-default  => $mt,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
}																		# Closes the multiple_match subroutine; Camel3 6.2, Cookbook 10.0.


sub no_match{												# Begins the no_match subroutine; Camel3 6.2, Cookbook 10.0.

	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1,
																		# CGI 11.2 (277).
	print $q->start_html(												# Uses the start_html function from CGI.pm to print the ending HTML 
			-title=>'No Search Text Words Found', 										# tags; CGI.pm 255, CGI 5.3 (110).
			-style=>{-src=>"$quotationFinderCss"}, 
			-expires=>'-1d', 
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		);

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );													# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
  
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>
      <h5>No Search Text Words Found</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      QuotationFinder could not find any search text words.
      <p>Try again by clicking <a href='$su'>here</a>.
    </td>
  </tr>
</table>
HTML

	print $q->end_html;													# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
}																		# Closes the no_match subroutine; Camel3 6.2, Cookbook 10.0.


sub count_refTextWords{														# Begins the count_refTextWords subroutine; Camel3 6.2, Cookbook 10.0. This
																		# subroutine counts the entries in the search text database. 
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1,
																		# CGI 11.2 (277).
	error( $q, "userDir is an empty string, I'm in sub count_refTextWords." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub count_refTextWords." ) if ($searchDir eq "");
	my $mldb = tie %refText, 'MLDBM', $mldbRefFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbRefFile is $mldbRefFile $!" );
																		# Associates the database file whose path is stored in the mldbRefFile
																		# variable with the refText hash so that, using the MLDBM module, any
																		# changes to the hash are saved to the file (which is created with 
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), 10.2 (241), DBI 2.7 (32), 2.9 (51), 
																		# Cozens 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	@wordResults = keys (%refText);									# Stores the keys of the refText hash in the wordResults array; 
																		# Learning 5.4.1. This allows us to easily count the records in the
																		# search text hashes later on.
	
	untie %refText;												# Closes $mldbRefFile; Cookbook 14.1, CGI 10.2 (241).

}																		# Closes the count_refTextWords subroutine; Camel3 6.2, Cookbook 10.0.


sub print_navigation {													# Begins the print_navigation subroutine; Camel3 6.2, Cookbook 10.0. 
																		# This subroutine displays the navigation page.
															# The next block of code is a here document to print out the top part of the
															# HTML page.  
	
	my ( $q, $id, $mo, $se ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
															# The $en and $mt variables are not passed to this subroutine as they are created 
															# afresh in the following lines of code.
	@enMt = get_encoding_and_matching( $q, $id, $mo, $se, $en, $mt, $su ) unless ($se eq "");		# 
	($en, $mt) = @enMt;
	$searchCount = count_search_texts( $q, $id ) unless ($id eq "");
	
#The following block of code stores HTML links in private variables that exist only within the file; CGI 11.2 (284).
	#DIESER CODE IST JETZT IN sub navigation_header VERDOPPELT. ELEGANTER WÄRE ES, DIESE VARIABLEN FÜR BEIDE SUBROUTINEN GEMEINSAM HERZUSTELLEN,
	#ABER AUS IRGENDEINEM GRUND BLEIBT DANN $id IM LINK LEER, AUCH WENN VORHER my $id = $q->param( "id" ) STEHT.
	my $addRefTextLink =
		$q->a( { href => "$qfUrl?action=addRefText&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "Enter" );
	my $chooseRefTextLink =
		$q->a( { href => "$qfUrl?action=chooseRefText&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "choose" );
	my $viewRefTextLink =
		$q->a( { href => "$qfUrl?action=viewRefText&page=$page&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "View" );
	my $addRefTextWordsLink =
		$q->a( { href => "$qfUrl?action=addRefTextWords&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "add" );
	my $modifyRefTextWordsLink =
		$q->a( { href => "$qfUrl?action=modifyRefTextWords&page=$page&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "modify" );
	my $deleteRefTextWordsLink =
		$q->a( { href => "$qfUrl?action=deleteRefTextWords&page=$page&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "delete" );
	my $newScoreLink =
		$q->a( { href => "$qfUrl?action=newScore&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "Find" );
	my $viewScoreLink =
		$q->a( { href => "$qfUrl?action=viewScore&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "View" );

	print $q->start_html(												# Uses the start_html function from CGI.pm to print the ending HTML 
			-title=>'QuotationFinder Navigation', 						# tags; CGI.pm 255, CGI 5.3 (110).
			-style=>{-src=>"$quotationFinderCss"}, 
			-expires=>'-1d', 
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		);

	print <<HTML;
<table width="750">
  <tr> 
    <td width="150" height="120">&nbsp;</td>
    <td valign="bottom">
      <table width="588" cellpadding="10">
        <tr> 
          <td> 
            <h1>QuotationFinder</h1>
HTML

	if ($se ne "") {
		print <<HTML;
            <p>Current Search Text: $se</p>
HTML
	}

	print <<HTML;
          </td>
        </tr>
      </table>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>
      <table width="360" cellpadding="10">
        <tr valign="top"> 
          <td class=roman height="180" bgcolor="#CCFFFF" width="180"> 
            $addRefTextLink<br>
            a new<br>
HTML

#	if (-e "$mldbSearchFile") {											# If the file whose name is stored in the mldbSearchFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7. We only want to 
																		# provide users with a link to choose a previously entered search text
																		# if one exists.

#	my $paramList;
#	foreach my $name ( param() ) {										# For debugging; CGI.pm 63.
#		my $value = param($name);
#		$paramList .= "$name: $value<br>";
#	}
#	error( $q, "paramList is <br>$paramList"); 

	my $choice;
	$choice = "yes" if ($searchCount > 1);
	$choice = "yes" if ($searchCount == 1 and $se eq "");
	if ($choice eq "yes") {
		print <<HTML;
            search text, or<br>
            $chooseRefTextLink<br>
            a previously<br>
            entered<br>
HTML
	}
	
	print <<HTML;
            search text.
          </td>
          <td class=roman bgcolor="#CCCCFF" width="180"> 
HTML

	if (-e "$mldbRefFile") {												# If the file whose name is stored in the mldbRefFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with links to view, add, modify,
																		# or delete records of the search text database if the latter exists.
		print <<HTML;
            $viewRefTextLink,<br>
            $addRefTextWordsLink,<br>
            $modifyRefTextWordsLink, or<br>
            $deleteRefTextWordsLink<br>
            words in<br>
            the current<br>
            search text.
HTML

	} else {
							
		print "            &nbsp;\n";									# Prints an HTML space if the condition above is not met; Learning 4.2.
																		# With some browsers, cells aren't displayed as expected if they're 
	}																	# empty.
	
	print <<HTML;
          </td>
        </tr>
        <tr> 
          <td class=roman height="180" bgcolor="#99FFFF" valign="top"> 
HTML

	if (-e "$mldbRefFile") {												# If the file whose name is stored in the mldbRefFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with a link to score text files
																		# if a search text database exists.
		print <<HTML;
            $newScoreLink<br>
            quotations<br>
            of the current<br>
            search text.
HTML

	} else {
							
		print "            &nbsp;\n";									# Prints an HTML space if the condition above is not met; Learning 4.2.

	}
	
	print <<HTML;
          </td>
          <td class=roman bgcolor="#99CCFF" valign="top"> 
HTML

	if (-e "$dbScoreTotalFile") {											# If the file whose name is stored in the dbScoreTotalFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with a link to view the score if
																		# the score exists.
		print <<HTML;
            $viewScoreLink<br>
            the results.
HTML

	} else {
							
		print "            &nbsp;\n";									# Prints an HTML space if the condition above is not met; Learning 4.2.

	}

	print <<HTML;
          </td>
        </tr>
      </table>
    </td>
  </tr>
</table>
HTML

	print $q->end_html;													# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
}																		# Closes the print_navigation subroutine; Camel3 6.2, Cookbook 10.0.


sub navigation_header{													# Begins the navigation_header subroutine; Camel3 6.2, Cookbook 10.0. 
																		# This subroutine provides navigation links to results pages.

	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;											# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).

	$searchCount = count_search_texts( $q, $id) unless ($id eq "");

	#The following block of code stores HTML links in private variables that exist only within the file; CGI 11.2 (284).
	#DIESER CODE IST JETZT IN sub print_navigation VERDOPPELT. ELEGANTER WÄRE ES, DIESE VARIABLEN FÜR BEIDE SUBROUTINEN GEMEINSAM HERZUSTELLEN,
	#ABER AUS IRGENDEINEM GRUND BLEIBT DANN $id IM LINK LEER, AUCH WENN VORHER my $id = $q->param( "id" ) STEHT.
	my $addRefTextLink =
		$q->a( { href => "$qfUrl?action=addRefText&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "Enter" );
	my $chooseRefTextLink =
		$q->a( { href => "$qfUrl?action=chooseRefText&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "choose" );
	my $viewRefTextLink =
		$q->a( { href => "$qfUrl?action=viewRefText&page=$page&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "View" );
	my $addRefTextWordsLink =
		$q->a( { href => "$qfUrl?action=addRefTextWords&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "add" );
	my $modifyRefTextWordsLink =
		$q->a( { href => "$qfUrl?action=modifyRefTextWords&page=$page&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "modify" );
	my $deleteRefTextWordsLink =
		$q->a( { href => "$qfUrl?action=deleteRefTextWords&page=$page&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "delete" );
	my $newScoreLink =
		$q->a( { href => "$qfUrl?action=newScore&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "Find" );
	my $viewScoreLink =
		$q->a( { href => "$qfUrl?action=viewScore&id=$id&mo=$mo&se=$se&en=$en&mt=$mt" }, "View" );


	print <<HTML;
<table width="750" border="0">
  <tr>
    <td width="150">
      <table width="150" cellpadding="2">
        <tr valign="top">
          <td class=small height="75" width="75" bgcolor="#CCFFFF">
HTML

	if ($id ne "") {													# If the value contained in the id variable is not an empty string, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with a link to enter or choose
																		# a search text after they have identified themselves.
		print <<HTML;
            $addRefTextLink<br>
HTML

#		if (-e "$mldbSearchFile") {										# If the file whose name is stored in the mldbSearchFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7. We only want to 
																		# provide users with a link to choose a previously entered search text
																		# if one exists.
		my $choice;
		$choice = "yes" if ($searchCount > 1);
		$choice = "yes" if ($searchCount == 1 and $se eq "");
		$choice = "yes" if ($searchCount == 1 and $q->param("addRefNameSubmit"));
		if ($choice eq "yes") {
			print <<HTML;
            or<br>
            $chooseRefTextLink<br>
HTML
		}
	
		print <<HTML;
            search<br>
            text.
HTML

	} else {
							
		print "            &nbsp;\n";									# Prints an HTML space if the condition above is not met; Learning 4.2.

	}

	print <<HTML;
          </td>
          <td class=small width="75" bgcolor="#CCCCFF">
HTML

	if (-e "$mldbRefFile") {												# If the file whose name is stored in the mldbRefFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with links to view, add, modify,
																		# or delete records of the search text database if the latter exists.
print <<HTML;
            $viewRefTextLink,<br>
            $addRefTextWordsLink,<br>
            $modifyRefTextWordsLink, or<br>
            $deleteRefTextWordsLink<br>
            words.
HTML

	} else {
							
		print "            &nbsp;\n";									# Prints an HTML space if the condition above is not met; Learning 4.2.

	}

	print <<HTML;
          </td>
        </tr>
        <tr valign="top">
          <td class=small height="75" bgcolor="#99FFFF">
HTML

	if (-e "$mldbRefFile") {												# If the file whose name is stored in the mldbRefFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with a link to score text files 
																		# if a search text database exists.
		print <<HTML;
            $newScoreLink<br>
            quotes.
HTML

	} else {
							
		print "            &nbsp;\n";									# Prints an HTML space if the condition above is not met; Learning 4.2.

	}

	print <<HTML;
          </td>
          <td class=small bgcolor="#99CCFF">
HTML

	if (-e "$dbScoreTotalFile") {											# If the file whose name is stored in the dbScoreTotalFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with a link to view the score if
																		# the score exists.
		print <<HTML;
            $viewScoreLink<br>
            results.
HTML

	} else {
							
		print "            &nbsp;\n";									# Prints an HTML space if the condition above is not met; Learning 4.2.

	}

	print <<HTML;
          </td>
        </tr>
      </table>
    </td>
    <td width="588">
      <h6>QuotationFinder</h6>
HTML

	if ($se ne "") {
		print <<HTML;
      <p>Current Search Text: $se</p>
HTML
	}
#	my @names = $q->param;
#	print "            names is '@names'<br>\n";
#	print "<table><tr><td>param:";
#	foreach my $name ($q->param) {
#		print "<br>$name is\n";
#		foreach my $value ( $q->param( $name) ) {
#			print "  '$value'\n";
#		}
#	}
#	print "</td><td>";
#	print "            at_:<br>\n";
#	print "            id is '$id'<br>\n";
#	print "            mo is '$mo'<br>\n";
#	print "            se is '$se'<br>\n";
#	print "            en is '$en'<br>\n";
#	print "            mt is '$mt'<br>\n";
#	print "            su is '$su'<br>\n";
#	print "</td></tr></table>";

	print <<HTML;
    </td>
  </tr>
HTML

}																		# Closes the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.


sub filter{													# Begins the filter subroutine. 
	my $temp = $_[0];											# Sets a variable called $temp to the value of what we passed to
															# the subroutine. 
	$temp =~ s/\|//; # Remove pipe symbols in text.			# Removes any pipe symbols from the $temp variable. Since we
															# used the pipe symbol as the field delimiter in the database, any pipe
															# symbols in the records, other than the ones we put if for the database,
															# will cause erratic results. 
	return ($temp);											# Returns the $temp variable from the subroutine. 
}																		# Closes the filter subroutine; Camel3 6.2, Cookbook 10.0.
															# BRAUCHEN WIR EINEN FILTER FÜR IRGENDWAS? DANN HABEN WIR HIER EIN MODELL. AM SCHLUSS
															# AUSKOMMENTIEREN!


sub print_message{														# Begins the print_message subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine displays a message to the user.
	my ( $q, $id, $mo, $se, $en, $mt, $su, $message, $note ) = @_;										# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the message, q, and id private variables, respectively; Ca-
																		# mel3 6.2.1, CGI 11.2 (277).
#	$la = $q->param('la') || 'viewNavigation';
#	$su =~ s/action=.+?;/action=$la;/;
	
	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Message',											# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form;

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );												# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
	
#	$searchCount = 0 unless (-e $mldbSearchFile);						# Assigns the value of 0 to the searchCount varibale unless the file
																		# the name of which is stored in the mldbSearchFile variable exists.
	$searchCount = count_search_texts( $q, $id ) unless ($id eq "");

															# The next block of code is a here document that prints out some
															# information to the user letting them know that the database did
															# something and provides them with a link out. 
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>$message</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	if ($note) {
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      $note
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}

	print <<HTML;
  <tr> 
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="viewNavigation" value="View Navigation Page">
    </td>
  </tr>
HTML

	unless ($q->param( "deleteRefSubmit" ) and $searchCount == 0) {
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
	  To return to where you came from click <a href='$su'>here</a>.
    </td>
  </tr>
</table>
HTML
	}
	
	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "mt",
				-default  => $mt,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
#	exit;
	
}																		# Closes the print_message subroutine; Camel3 6.2, Cookbook 10.0.


sub print_user_error{													# Begins the print_user_error subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine displays a user error message to the user.
	my ( $q, $id, $mo, $se, $en, $mt, $su, $message ) = @_;										# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the message, q, and id private variables, respectively; Ca-
																		# mel3 6.2.1, CGI 11.2 (277).
#error( $q, "la is $la" );
#	$la = $q->param('la') || 'viewNavigation';
#	$su =~ s/action=.+?;/action=$la;/;
	
	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'User Error',											# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		);

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );												# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.

															# The next block of code is a here document that prints out some
															# information to the user letting them know that the database did
															# something and provides them with a link out. 
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>Error</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      $message
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
	  Try again by clicking <a href='$su'>here</a>.
    </td>
  </tr>
</table>
HTML
#  <tr> 
#    <td>&nbsp;</td>
#    <td class=roman>
#	  Try again by clicking <a href='$qfUrl?action=$la&id=$id'>here</a>.
#    </td>
#  </tr>
#</table>
#HTML

	print $q->end_html;													# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
	exit;
	
}																		# Closes the print_user_error subroutine; Camel3 6.2, Cookbook 10.0.


sub create_score{														# Begins the create_score subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine does the actual scoring of the matched texts.

	### This is a very long part of the program. I did not break it up into subroutines for performance reasons; Camel 8.3.1. 

	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my ($scoreSize, $uploadSize, $processedSize, $newRecsCounter);
	my ($word, $wordUni, $file, @files, @records);										# Declares private variables that exist only within the innermost en-
	my (%inwords, %seenWorks, %score, %scoreWork, %scoreTotal);						# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.

	my $oldScoreWorkFile = 1 if -e $dbScoreWorkFile;					# We need to remember if there was a dbScoreWorkFile when we started 
																		# the search process so that we can give users a better search results 
																		# message.
	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Search Progress',											# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form;

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );												# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.

	my $numberOfFiles = @fileNames;										# Actually, the number of elements in the fileNames array always cor-
																		# responds to the un (upload number) variable, as empty array elements
																		# are not being removed
	foreach $file (@fileNames) {
	
		$uploadSize += -s $file;										# Camel3 3.10.
		
	}
#	error( $q, "uploadSize is $uploadSize" );							# For debugging
	
	$searchCount = count_search_texts( $q, $id) unless ($id eq "");

	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
  <td>&nbsp;</td>
    <td> 
      <h5>Search Progress</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Results" target="Help">Help&nbsp;</a></td>
    <td class=roman>
      Please click the View Results button when it appears at the bottom of the page.
HTML

#	if ($numberOfFiles > 1) {
#		print "      <p>QuotationFinder has now processed the following files and texts:\n";
#	} elsif ($numberOfFiles == 1) {
#		print "      <p>QuotationFinder has now processed the following texts:\n";
	if ($numberOfFiles > 0) {
		print "      <p>QuotationFinder has now processed the following:\n";
	} else {
		error( $q, "No files, I'm in sub create_score." );	# For debugging
	}

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
</table>
HTML

	### The following chunk of the program builds the inwords hash, our lookup table, from the wordlist file created by the user.

	error( $q, "userDir is an empty string, I'm in sub create_score." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub create_score." ) if ($searchDir eq "");
	my $mldb = tie %refText, 'MLDBM', $mldbRefFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbRefFile is $mldbRefFile $!" );
																		# Associates the database file whose path is stored in the mldbRefFile
																		# variable with the refText hash so that, using the MLDBM module, any
																		# changes to the hash are saved to the file (which is created with 
																		# write access for us but no one else in case it doesn't exist yet); 
																		# Cookbook 14.1, CGI 7.4 (191), 10.2 (241), DBI 2.7 (32), 2.9 (51), 
																		# Cozens 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	foreach $key (keys %refText) {									# Traverses the refText hash, so that we can perform an action on
																		# each entry; Cookbook 5.4, Camel 4.7.5.3.
		my ($posWordRef, $genFreq, $form, $cognate);							# Declares private variables that exist only within the innermost en-
		my ($wordLower, $formLower, $cognateLower);
		my (@forms, @cognates);						# closing block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
		
		$word		= $refText{$key}{'Word'};
		$posWordRef	= $refText{$key}{'PosWordRef'};
		$genFreq	= $refText{$key}{'GenFreq'};
		@forms		= @{ $refText{$key}{'Forms'} };
		@cognates	= @{ $refText{$key}{'Cognates'} };
		$wordUni	= $refText{$key}{'WordUni'};
		
		# In order to make user input from the Word, Forms, and Cognates fields more fool proof, we remove duplicates, and we remove Word from 
		# the Forms array as well as Forms from the Cognates array and then treat input from theses fields separately. This makes it irrelevant
		# if users have repeated their entries within the same or in some other field.
		
		my (%seenForms, %seenCognates);

		foreach $form (@forms) {										# Cookbook 4.6.
			$seenForms{$form}++ unless $form eq $word;
		}
		my @uniqueForms = keys %seenForms;		
		
		foreach $cognate (@cognates) {								# Cookbook 4.6.
			$seenCognates{$cognate}++ unless $seenForms{$cognate};
		}
		my @uniqueCognates = keys %seenCognates;		
		
		$wordLower = lc($word);											# Makes $word lowercase and puts it in $wordLower; Cookbook 1.9.
		push (@{ $inwords{$wordLower} }, $posWordRef, $genFreq, $wordUni, "word");			# Creates a new entry for the inwords hash(!), using the current value
																		# of $wordLower as the key and the position in search text and general fre-
																		# quency information as values; Camel 4.7.2.2, Cookbook 11.2.
																		# We'll use this hash as our lookup table in order to have fast access
																		# to position and frequency information about our search terms; Camel
																		# 8.3.1, Cookbook 4.7.

		foreach $form (@uniqueForms) { 									# Executes the body of the loop once for each element of the  
																		# uniqueForms array and puts the element in $cognate; Learning 
																		# 1.5.16, 4.5.
			$formLower = lc($form);										# Makes cognate lowercase and puts it in $cognateLower; Cookbook 1.9. 
			push (@{ $inwords{$formLower} }, $posWordRef, $genFreq, $wordUni, "form");			# Creates a new entry for the inwords hash(!), using the current value
																		# of $cognateLower as the key and the position in search text and general fre-
																		# quency information as values; Camel 4.7.2.2, Cookbook 11.2.
		}																# Closes the foreach $form loop; Nutshell 4.3.

		foreach $cognate (@uniqueCognates) { 							# Executes the body of the loop once for each element of the  
																		# uniqueCognates array and puts the element in $cognate; Learning 
																		# 1.5.16, 4.5.
			$cognateLower = lc($cognate);								# Makes cognate lowercase and puts it in $cognateLower; Cookbook 1.9. 
			push (@{ $inwords{$cognateLower} }, $posWordRef, $genFreq, $wordUni, "cognate");			# Creates a new entry for the inwords hash(!), using the current value
																		# of $cognateLower as the key and the position in search text and general fre-
																		# quency information as values; Camel 4.7.2.2, Cookbook 11.2.
		}																# Closes the foreach $cognate loop; Nutshell 4.3.

	}																	# Closes the foreach $key loop; Nutshell 4.3.

	untie %refText;														# Closes $mldbRefFile; Cookbook 14.1, CGI 10.2 (241).
#	print Dumper(\%inwords);										# For debugging.


	### The following chunk of the program looks at every word of every text in the file the user selects, and checks if the word is in our lookup
	### table. If so, the program performs some calculations on it. If these calculations result in a sufficient score for the text, both it and 
	### the results are retained--otherwise not.

	error( $q, "userDir is an empty string, I'm in sub create_score." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub create_score." ) if ($searchDir eq "");
	my $dbWork = tie %seenWorks, 'DB_File', $dbSeenWorksFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File file: dbSeenWorksFile is $dbSeenWorksFile $!" );
																		# Associates the database file whose path is stored in the dbSeenWorksFile-
																		# File variable with the score hash so that, 
																		# using the DB_File module, any changes to the hash are saved to 
																		# the file (which is created with write access for us but no one else 
																		# in case it doesn't exist yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 
																		# (32), 2.9 (51), Cozens 435.
	undef $dbWork;														# Frees up the memory associated with the objects; Camel3 29.2.187, 
																		# Cookbook 11.0.
							 						
	foreach $file (@fileNames) {										# Executes the body of the loop once for each element of the files ar-
																		# ray and puts the element in $fileName; Learning 1.5.16 and 4.5.	
		my ($passage, $passageCounter, $fileLineCounter, $progressCounter, $clcltCounter, $hitLine, $percentOld, $workNew, $workKey, $workKeyNew, @text, @matchLines);	# Declares private variables that exist only within the innermost en-
		my ($author, $authorNext, $reference, $referenceNext, $text, $textNext);	# Declares private variables that exist only within the innermost en-
																		# closing block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
		my $indexMemento = 0;											# Puts an initial value of zero in $indexMemento; Camel3 33 and perl-
																		# diag.pod on Use of uninitialized value.
		my $textEnd = 0;

		my $blank = 0;
		
		my $matchedWords;										# for debugging
		
		next if ($file eq "");											# Skips processing the current file variable if it is blank; Camel3 
																		# 1.6.2.4. This occurs whenever blank filename fields remain on a 
																		# file upload form.
		print <<HTML;
<table width="750" border="0">
  <tr>
    <td width="150">&nbsp;</td>
    <td width="588">
      $file
    </td>
  </tr>
</table>
HTML
		local $/ = "\015" if $fo eq "Pandora";						# Sets the input record separator to \015 (carriage return) locally
																		# if the value stored in the fo(rmat) variable is "Pandora"; MacPerl
																		# 9.3 (131), Munging 6.3.1 (112), Camel3 25.1. Files exported by Pan-
																		# dora have (classic) Macintosh newlines rather than Unix (\012, i.e.
																		# line feeds) or DOS (\015\012) newlines.
		local $/ = "\\par" if $fo eq "TLG_Workplace";						# Sets the input record separator to \par locally if the value stored 
																		# in the fo(rmat) variable is "TLG_Workplace"; MacPerl 9.3 (131), Munging 
																		# 6.3.1 (112), Camel3 25.1. Files exported by TLG Workplace do not 
																		# seem to have line endings, so we use the RTF paragraph tag as input
																		# record separator.

		### OPTIMIERUNGSPOTENTIAL: AUFGRUND VON JE 3 STD DAUERNDEN TESTLÄUFEN IST ZU ERWARTEN, DASS DIE GESCHWINDIGKEIT VON QF UM CA. 18% GE-
		### STEIGERT WERDEN KÖNNTE, WENN MAN DIE FOLGENDE if ($fo eq "CLCLT" ... ) BEDINGUNG AUS DEM while (<$file>) LOOP HERAUSNEHMEN WÜRDE. 
		### DIES HÄTTE ALLERDINGS ZUR FOLGE, DASS MAN DIE FOLGENDEN 800 ZEILEN CODE JE FÜR CLCLT, PANDORA UND TLG_WORKPLACE WIEDERHOLEN MÜSSTE
		### (ES SCHEINT NICHT MÖGLICH ZU SEIN, DIE GEMEINSAMEN CODE-TEILE IN SUBROUTINEN AUSZULAGERN, WEIL MAN DAZU HASHES AN SUBROUTINEN WEI-
		### TERREICHEN KÖNNEN MÜSSTE). DARAN SOLLTE MAN ALSO ERST DENKEN, WENN DIE 800 ZEILEN FERTIG SIND. ODER MAN WARTET AUF PERL 6.
		
		LINE: while (<$file>) { 												# Iterates through the file line by line. Diamond operator (angle
																		# brackets) reads a single line of the text file at the beginning of  
																		# each cycle through the foreach loop; Learning 6.2. While statement  
																		# executes the block as long as there are lines left; Learning 1.5.4,  
																		# 4.3, Camel 4.6.2; cf. Cookbook 7.0, Nutshell 4.9.
			check_upload( $q, $id, $mo, $se, $en, $mt, $su, $fo, $file ) if $. == 1;
			
			++$fileLineCounter;											# Autoincrement
			
			$processedSize += length($_);									# CGI.pm 3.9 (152).

			if ($fo eq "CLCLT") {
			
				if (/Excerpta CLCLT-(\d)/ .. /<<< 1 >>>/) {					# If a pattern that begins with "Excerpta" and ends with <<< 1 >>> is 
																			# matched, the following block of code is executed; Cookbook 6.8. This 
																			# pattern is found at the beginning of Cetedoc export files.
					$clcltCounter = 1;
					next LINE;													# Skips the current loop iteration; Camel 1.6.2.4. 
				
				} elsif (/Cl\. \d\d\d\d/ || /liber : \d+,/ || /cap\. : \d+,/ || /par\. : \d+/ || /versus : \d+/ || /linea : \d+/ || /pag\. : \d+/) {		# If one of the patterns between "/" is machted,
																		# we execute the following block of code; Learning 1.5.3, Cookbook 6.2.

					chomp;												# Deletes trailing newline character; Camel3 29.2.11.
					
					$passage = $_;										# Stores the pattern that was matched in a variable named passage; 
																		# Camel3 1.7.
					$hitLine = $fileLineCounter - 1;					# The hit the CLCLT software found is always in the line following the
																		# passage indication (+ 1). As $work and $passage take up two lines in  
																		# the file, we need to subtract 2 from fileLineCounter to get the correct
																		# line number (- 1).
					++$passageCounter;
					
					print "<br>WARNING: clcltCounter NOT IN SYNC WITH passageCounter!<br>" if ($passageCounter != $clcltCounter);	# For debugging.
					
					$work = pop(@text);									# Removes the last element of the text array and puts it in a variable
																		# named work; Learning 3.4.3. We know that if we have matched the cla-
																		# vis line in a Cetedoc export file, the last element of the previous
																		# line, stored in @text, indicates the work.	
					$workKey = $work;									# Starts building a workKey variable that identifies the work unambigu-
																		# ously by storing the work variable in it; Camel3 1.5.3. We will use    
																		# this variable as a hash key later on, for which it has to be unique-- 
																		# passage info by itself is usually not unique.
					
					if (/(Cl\. \d\d\d\d.*?), /) {						# If the pattern between the "/" is matched, the following block of 
																		# code is executed; Camel 2.4.2. Non-greedy matching by way of "?": 
																		# Camel 1.7.2
						$workKey .=	$1;									# Appends $1, i.e. the part of the matched pattern between parentheses,
																		# to the workKey variable; Learning 2.6.1, Camel 2.5.17, 2.4.1.2.
					}													# Closes the if block; Nutshell 4.3.

					while (/: (\d+)/g) {								# While the pattern between "/" is found, the following block of code
																		# is executed; Camel 2.4.
						if    ($1 =~ m/(\d\d\d\d)/) {$workKey .= " $1";}	# If $1, i.e. the part of the matched pattern between parentheses, con-
						elsif ($1 =~ m/(\d\d\d)/)  {$workKey .= " 0$1";}	# tains a particular number of digits, we append an inversely corre-
						elsif ($1 =~ m/(\d\d)/)   {$workKey .= " 00$1";}	# sponding number of zeroes to the workKey variable; Learning 2.6.1,
						else                     {$workKey .= " 000$1";}	# Camel 2.5.17. We do this so that we'll have automatic numerical sort-
					}														# ing later on.
	
					next LINE;											# Skips the current loop iteration; Camel 1.6.2.4. This pattern is 

				} elsif (/<<< Memento/) {								# Else, if the pattern between "/" is matched, the following block of
																		# code is executed; Learning 4.2, Camel 1.6.1.1.
					$indexMemento = $.;									# Stores the current line input number in a variable named index-
																		# Memento; Camel 2.9.3, Nutshell 4.4.1. This variable will be used
																		# later to separate memento text (Cetedoc info) from other text.
				} elsif (/<<< SENTENTIAE - INQUISITIO IN UOL/) {		# Else, if the pattern between "/" is matched, the following block of
																		# code is executed; Learning 4.2, Camel 1.6.1.1.
					$passageCounter = 0;
					next LINE;													# Skips the current loop iteration; Camel 1.6.2.4. 
				
				} elsif (/<<< (\d+)/) {
					
					$clcltCounter = $1;
					$textEnd = "yes";
				
				} elsif (eof) {
					
					$textEnd = "yes";
				
				}
				
			} elsif ($fo eq "Pandora") {

				if (/Exported from Pandora/) {					# If a pattern that begins with "Exported from Pandora" and ends with
																			# a blank line is matched, the following block of code is executed;
																			# Cookbook 6.8.
					$blank = 2;
					next LINE;													# Skips the current loop iteration; Camel 1.6.2.4. This pattern is 
																			# found at the beginning of Cetedoc export files. We can ignore it.
				}
				elsif (/TLG\d\d\d\d/ or /DOCCAN\d/ or /Search in:/ or /Search for:/) {					# If a pattern that begins with "Exported from Pandora" and ends with
					next LINE;													# Skips the current loop iteration; Camel 1.6.2.4. This pattern is 
				}
				elsif ($blank == "2" or /.+, .+ ([lL]ine|ln) /) {			### BLANK ZÄHLER FUNKTIONIERT NICHT!!! MUSS IN ORDNUNG GEBRACHT WERDEN
																	### WEIL SONST ALLE TEXTE ÜBERGANGEN WERDEN, DIE KEIN [lL]ine IN DER
																	### ÜBERSCHRIFT HABEN!!!!!!!!!!!!!
					next LINE if (/^$/);								# Some new texts start after a total of 2 blank lines, some only after 3.
					$work = $workNew;
					$workKey = $workKeyNew;
					chomp $workKey;
					$workKey =~ s/&1?//g;
#					$workKey =~ s/[\.\*\?\+\[\]\(\)\{\}\^\$\|\\\/ ,%;*]//g;
					$workNew = $_;
					$workKeyNew = $workNew;
					$blank = 0;
					$textEnd = "yes";
					next LINE;													# Skips the current loop iteration; Camel 1.6.2.4. This pattern is 
				} elsif (/^$/) {									# Else, if the pattern between "/" is matched, the following block of
																			# code is executed; Learning 4.2, Camel 1.6.1.1.
					++$blank;
					next LINE;													# Skips the current loop iteration; Camel 1.6.2.4. This pattern is 
																			# found at the beginning of Cetedoc export files. We can ignore it.
				} elsif (eof) {
					$textEnd = "yes";
				}

			} elsif ($fo eq "TLG_Workplace") {

				my $par = $_;
					
				next LINE if $par =~ /deftab720|List name:|Allowable interval between words:|Total number of matches:/;
				
				$par =~ s/\\f1|\\f2 |\\f3 |\\par//g;
				
				if ($par =~ /\\fs24 (.*)/) {
				
					my $tail = $1;
			
					if ($tail =~ /Search for:/) {
			
						next LINE;
			
					} elsif ($tail =~ /^ /) {							# If there's a total of 2 spaces after "fs24," the name of the author
																		# follows. This arrangement results from saving an individual author's
																		# results as accessed from a "summary" list in TLG Workplace 9.
						$tail =~ s/^\s+//;								# Removes leading and trailing whitespace; Cookbook 1.14.
						$tail =~ s/\s+$//; 
			
						$author = $tail;
						
						$referenceNext = "on";
						
					} else {
			
						$tail =~ s/^\s+//;								# Removes leading and trailing whitespace; Cookbook 1.14.
						$tail =~ s/\s+$//;
			
						$reference = $tail;
						
						$textNext = "on";
						
					}
				
				} elsif ($par =~ /Stats Only Search Automatically Enabled/) {
				
					print <<HTML;
<table width="750" border="0">
  <tr>
    <td width="150">&nbsp;</td>
    <td width="588">
      The following TLG Workplace message has been found:
      <br>&quot;WARNING: Stats Only Search Automatically Enabled!&quot;
      <br>This means that in '$file'
      <br>you have tried to export more text than TLG Workplace allows in one file, 
      <br>so that QuotationFinder's results are now incomplete. Try restricting your 
      <br>search in TLG Workplace before exporting. Then return to QuotationFinder 
      <br>to process the file again. (You can keep QuotationFinder's previous 
      <br>results. This will greatly speed up the new search.)
      <br>For further information click <a href="/quotationfinder/QuotationFinderHelp.html#Search_Progress" target="Help">here</a>.
    </td>
  </tr>
</table>
HTML
					last LINE;
							
				} elsif ($par =~ /-----------------------------------------|Number of matches:/) {
				
					$authorNext = "on";
							
				} elsif ($authorNext eq "on") {
				
					$par =~ s/^\s+//;									# Removes leading and trailing whitespace; Cookbook 1.14.
					$par =~ s/\s+$//; 
			
					$author = $par;
					
					$authorNext = "off";
					$referenceNext	= "on";
				
				} elsif ($referenceNext eq "on") {
				
					$par =~ s/^\s+//;									# Removes leading and trailing whitespace; Cookbook 1.14.
					$par =~ s/\s+$//; 
			
					$reference = $par;
					
					$referenceNext = "off";
					$textNext = "on";
				
				} elsif ($textNext eq "on") {
				
					@text = split /\\line/,  $par;						# Camel3 29.2.161
					
					while (@text) {										# Camel3 1.6.2.1
					
						my $lastBlank = pop @text;						# Camel3 29.2.111
					
						if ($lastBlank =~ /\S/) {						# If the last element in the text array contains any non-
																		# whitespace character (i.e. is not blank)... Nutshell 4.6.4.
							push @text, $lastBlank;						# Camel3 29.2.116							
							last;										# Camel3 1.6.2.4
							
						} else {
						
							next;										# Camel3 1.6.2.4
							
						}
					}
							
					while (@text) {										# Camel3 1.6.2.1
					
						my $firstBlank = shift @text;					# Camel3 29.2.149
					
						if ($firstBlank =~ /\S/) {						# If the first element in the text array contains any non-
																		# whitespace character (i.e. is not blank)... Nutshell 4.6.4.
							unshift @text, $firstBlank;					# Camel3 29.2.190							
							last;										# Camel3 1.6.2.4
							
						} else {
						
							next;										# Camel3 1.6.2.4
							
						}
					}
							
					if ($author) {
			
						$work = "$author, $reference";
						
					} else {
					
						$work = "$reference";
					
					}
					
					$workKey = $work;
					
					foreach my $line (@text) {
			
			#			$line = convert_symbolgreek_to_beta($line);
						$line = convert_sgkclassic_to_beta($line);
			
					}
					
					$textNext = "off";
					$textEnd = "yes";
					$referenceNext = "on";
					
				}
			}

			if ($textEnd ne "yes") {								# If the ($textEnd ne "yes") condition is met, the following block of
																		# code is executed; Learning 4.2, Camel 1.6.1.1.
				push (@text, $_) unless $fo eq "TLG_Workplace";										# The current line read from the Cetedoc file is added to the text ar- 
																		# ray; Learning 3.4.3, Camel 3.2.112. If the line read from the file 
																		# doesn't match any of the patterns above, it gets stored as a text 
																		# line.
				next LINE;
			
			} else {									# Else, if the ($textEnd ne "yes") condition is not met, the following block of code is 
																		# executed; Learning 4.2, Camel 1.6.1.1. The pattern indicates the be-
																		# ginning of a new text in Cetedoc files, which means that we can start
																		# processing the info we have gathered about the old one.
				my $textLineCount = @text;									# For debugging; Learning 2.3.4, Cozens 303.
				
				$work = process_work_title($work) unless $fo eq "CLCLT";		# Calls the process_work_title subroutine, passes it the work va-
																		# riable, and then passes the result of the subroutine back to the
																		# work variable; Camel3 6.2.1. Deals with Beta code formatting 
																		# characters and Greek in work titles.
				unless ($work eq "" or $textLineCount < 1) {

					my $progressWork = "$work";
					$progressWork .= " $passage" unless $passage eq "";
					my $percent = int $processedSize / $uploadSize * 100 unless $uploadSize == 0;

					unless ($percent eq $percentOld) {

						# Browsers tend to buffer table HTML until they encounter an end-table tag. So, we start and end a table for every 
						# list item we want to display, as we don't want users to have to wait.
						# Also, browsers tend to buffer HTML until they have enough to fill a page (or the document has fully loaded, of  
						# course). Now, when people upload very large files, it could take a while until 20 percent of the data is processed
						# (20 percent = 20 lines of list entries = one HTML page). So, we list ALL of the first one hundred works processed 
						# (this fills the first page, the user is reassured that progress is being made), but only one for every percentage 
						# point after that, because otherwise the list can grow to the size of dozens of MB.
						
						++$progressCounter;
						$percent = "&#139; 1" if $percent == 0;
						my $onePercentMessage = "\n      <br>&nbsp;\n      <p>&#091;Progress only shown in full percentage point increments from now on.&#093;" if ($percent == 1 and $progressCounter > 1);
						print <<HTML;
<table width="750" border="0">
  <tr>
    <td width="150">&nbsp;</td>
    <td width="588">
      <ul>
        <li>$percent&#037; ...working on $progressWork...
      </ul>$onePercentMessage
    </td>
  </tr>
</table>
HTML
						$percentOld = $percent;
					}
				}

				
				my ($indexNewText, $lengthMemento, @memento, @originalText, @newText);	# Declares private variables that exist only within the innermost en-
				my ($line, $newLine, $chunk);							# closing block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
				
				my @wordsLine;

				my ($posWordCur, $posWordRef, $genFreq, $genFreqTotal, $relFreq);
				my (%countMatches, %position, %points);
				my (%allMovePos);

				my (%positionRef, %positionCur, %genFreqCur, %genFreqRef, %relFreqRef, %seen);

				my (@anyPosWordCur, @multiPosWordCur);
				
				my %allSumsPointsPos;
				my @sortedSumsPointsPos;
				my ($gapPosWordCur, $corePosWordCur, $coreLineCur, $corePosWordRef);

				my %allListsPosWordCur;
				my (@listPosWordCur, @sortedPosWordCur);
				my ($highestPosWordCur);
				my ($pointsDens, $pointsTotal);
				my ($n, $i, $j, $x, $y);
				
				my (@dataPerWord);
				my $movePos;
				

				my ($sumPointsPos, $sumPointsOcc);

				my $hits = 0;											# Puts an initial value of zero in $hits; Camel3 33 and perldiag.pod 
																		# on Use of uninitialized value.
				$textEnd = 0;
#					my $textSize = @text;
#					print "<p>textSize is $textSize, Dollar_ is $_, indexMemento is $indexMemento</p>";
				if ($indexMemento > 0) {								# If the value stored of the indexMemento variable is greater than 0, 
																		# the following block of code is executed; Camel3 1.5.6, 4.3.
					$indexNewText = $.;									# Stores the current line input number in a variable named index-
																		# Memento; Camel 2.9.3, Nutshell 4.4.1.
					$lengthMemento = $indexNewText - $indexMemento;	# Subtracts the indexMemento from the indexNewText variable, and
#					$lengthMemento = ($indexNewText - $indexMemento) - 1;	# Subtracts the indexMemento from the indexNewText variable, and
																		# then 1 from that, and stored the results in the lengthMemento vari-
																		# able; Camel3 1.5.3.
					@memento = splice (@text, -$lengthMemento);			# Removes all text array elements after the offset determined by the
																		# negative lengthMemento variable and stores them in the memento ar-
																		# ray; Camel 3.2.154, Cookbook 4.11. Now that we know the number of 
																		# lines taken up by the memento, we can simply remove that many lines
																		# from the text array to end up with the memento text.
					$indexMemento = 0;									# Resets the $indexMemento variable to 0 so that this block will only 
																		# be entered again if a new memento is found; Learning 4.4. Otherwise, 
																		# a text block of the size of the current memento would be spliced off 
																		# every text array until $indexMemento is reset by the above elsif 
																		# block...
				}														# Closes the if block; Nutshell 4.3.

#error( $q, "text is<br>@text<br>memento is<br>@memento<br>lengthMemento is $lengthMemento, indexNewText is $indexNewText, current line is $_" );
				$workKey =~ s/\W//g;

				unless ($fo eq "CLCLT") {
				
					my $newWorkKey;

					my @chunks = split /(\d+)/, $workKey;
					
					foreach my $chunk (@chunks) {										# We add zeros to the numbers in workkey so that we'll have automatic
						if ($chunk =~ /(\d+)/) {										# numerical sorting later on (when results are sorted by author and
							   if ($1 > 999999) {$newWorkKey .= "0$1";}					# work, chapter 17 will appear after chapter 2).
							elsif ($1 > 99999) {$newWorkKey .= "00$1";}
							elsif ($1 > 9999) {$newWorkKey .= "000$1";}
							elsif ($1 > 999) {$newWorkKey .= "0000$1";}
							elsif ($1 > 99) {$newWorkKey .= "00000$1";}
							elsif ($1 > 9) {$newWorkKey .= "000000$1";}
							else		  {$newWorkKey .= "0000000$1";}
						}
						else			{$newWorkKey .= $chunk;}
					}
					$workKey = $newWorkKey;
				}

				if (exists($seenWorks{$workKey})) {							# Checks to see if an entry on the text indicated by the $workKey vari-
																		# able is already stored in the seenWorks hash; Cookbook 5.2. This makes 
																		# the program more efficient--there is no need to score a text that 
																		# has been scored before.
#					print "<p>The score of workKey '$workKey' is already in the database.</p>";	# For debugging.
					@text = ();											# Empties the @text array; Learning 3.2, Camel 2.3.4.
					$fileLineCounter = 0;
					next LINE;												# Skips the rest of the elsif (/<<< \d/ or eof) block and jumps to the
																		# next item of the while (<FH>) loop; Learning 9.2, Camel 1.6.2.4. 
				} else {
				
#					$seenWorks{$workKey} = "$work $passage";
					$seenWorks{$workKey} = 1;							# We don't really need "$work $passage." This saves server disk space.
				
				}														# Closes the if (exists($seenWorks{$workKey})) block; Nutshell 4.3.

				# The following chunk of code goes through every word of the text of which we have just reached the end. It checks to see if 
				# the word is contained in the search text lookup hash, and, if so, records information on position and frequency. Also, it 
				# highlights the matched words in the text for display to the user.
				
				my ($hyphenated, $checkHyphenated, $textLineCounter);
				
				foreach $line (@text) {									# For each line stored in the text array, the following block of code
																		# is executed; Camel3 1.6.2.3.
					
					++$textLineCounter;									# Autoincrement
					
					chomp $line;
					
					$line =~ tr/*//d if ($fo eq "CLCLT");				# Removes asterisks from line variable; Learning 1.5.8, 15.5, Camel
																		# 2.4, Camel3 5.2.4.
					push @originalText, $line;							# We need an unchanged text for reliable text comparisons when we'll 
																		# eliminate duplicates later on. If we used @newText for that, the
																		# user could have made changes to the search text between searches 
																		# which would change the highlighting in @newText so that duplicates 
																		# could no longer be recognized as such.
					if ($hyphenated ne "" and $line !~ /&`?(.*)\$/) {	# Lines that consist of line and page numbers are skipped when pre-
																		# fixing hyphenated word parts.
						$line =~ s/^(\s+)//;							# Removes leading whitespace; Friedl 7.8.1 (290).
						my $leadingWhitespace = $1;
						$line = "$leadingWhitespace$hyphenated$line";	# Inserts first part of hyphenated word (from last line) between lead-
						$hyphenated = "";								# ing whitespace and the rest of the current line.
					}
					
					@wordsLine = split(/\s+/, $line);					# Splits the content of the line variable at whitespace (1 or more) and
																		# puts the results in the wordsLine array; Learning 7.6.1, Cookbook 8.3.

					if ($line =~ /\s(\S+?)-\s+?$/) {					# If the value stored in the line variable contains the pattern be-
																		# tween the slashes, the following block of code is executed; Camel3
																		# 5.6.2. (In Perl, +? is the non-greedy version of +; Friedl 83.) When 
																		# hyphenated words are encountered, the first part needs to be removed
																		# from the end of the current line and added to the beginning of the 
																		# next text line.
						$hyphenated = $1;
						pop @wordsLine;									# Removes the last element of the wordsLine array; Camel3 29.2.111.
					}

#$matchedWords .= "the matched words are: ";
					foreach $chunk (@wordsLine) {						# Iterates over every element of the wordsLine array; Camel 2.6.4.3.
																		# The advantage of this method over a while loop is that if you change
																		# an element of the array within the foreach loop, it actually gets
																		# changed in the array itself. We are using this fact in order to high-
																		# light matches in the output, as well as remove unwanted characters.
						my $wordFormCognate;
						
						$posWordCur += 1 if ($chunk =~ m/\w/);			# Increases the posWordCur counter by one if $chunk contains a word
																		# character; Learning 2.6.1.
						$word = lc($chunk);								# Converts word in $chunk to lowercase and puts it in $word; Cookbook 
																		# 1.9. The reason we are using two separate variables, $chunk and 
																		# $word, with similar content now is that we're changing one to be a 
																		# good pattern match while retaining the other for display to user.
#						$word =~ tr/_.,:;?!<>()[]//d;					# Removes remaining non-word characters from word variable; Learning
#						$word = tr/_.,:;?!<>()[]|'-\/=\\+@//d;			# Removes remaining non-word characters from word variable; Learning																		# 1.5.8, 15.5, Camel 2.4, 8.3, Friedl 77.
																		# 1.5.8, 15.5, Camel 2.4, Friedl 77. PRÜFEN !!!!!!!!!!!!!1
						$word =~ s/[^a-z]//g;
						$word =~ tr/vj/ui/ if ($fo eq "CLCLT");			# Replaces every occurrence of v and j by u and i, respectively; Camel3
																		# 5.2.4, CLCLT-3 manual, p. 64.
						if ($mt eq "pt") {					# Checks if $word is contained in inwords hash(!); Cookbook 4.8, 5.3,
																		# Camel4.4, Elements 8.1. The inwords hash is the lookup table created
																		# from search text user entries.
							foreach my $key (keys %inwords) {						# Cookbook 5.4.

								if ($word =~ /$key/) {					# Cookbook 6.0.
$matchedWords .= "$word ";
									push @matchLines, $textLineCounter;	# We will need this in order to establish a hitLine in TLG Workplace 
																		# and Pandora files.
									$chunk = "<b>$chunk</b>";					# Surrounds $chunk with HTML bold tags; Camel3 1.5.2. We highlight the
																				# word that the current text has in common with the search text.
		#							$chunk = "<span class=hilite>$chunk</span>";					# Surrounds $chunk with HTML bold tags; Camel3 1.5.2. We highlight the
																				# word that the current text has in common with the search text.
									
									my @values;									# Declares a private variable that exist only within the innermost en-
																				# closing block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.

									@values = @{ $inwords{$key} };				# Puts information on $key contained in the lookup hash in the values 
																				# array; Cookbook 11.2.

									while (@values) {							# While there are any elements left in the values array, the following
																				# block of code is executed; Learning A.3. Chapter 4, Camel 1.6.2.1. As
																				# the values array may contain more than one pair of position plus fre-
																				# quency information--the word may occur at various positions in the 
																				# search text--, we need to iterate through it.
										($posWordRef, $genFreq, $wordUni, $wordFormCognate) = splice(@values, 0, 4);	# Removes two elements from the values array, starting at
																				# pos. 0, and puts them in variables; Cookbook 4.11.
										if ($wordFormCognate eq "word") {

											$countMatches{$posWordRef}{word}++;	# Auto-increments the value stored under the $posWordRef key 
																		# of the outer hash and the word key of the inner hash by one; 
																		# Camel3 1.5.4, 9.4.3, Cookbook 5.14. 
																			
										} elsif ($wordFormCognate eq "form") {

											$countMatches{$posWordRef}{form}++;	# Auto-increments the value stored under the $posWordRef key 
																		# of the outer hash and the form key of the inner hash by one; 
																		# Camel3 1.5.4, 9.4.3, Cookbook 5.14. 
																			
										} elsif ($wordFormCognate eq "cognate") {

											$countMatches{$posWordRef}{cognate}++;	# Auto-increments the value stored under the $posWordRef key 
																		# of the outer hash and the cognate key of the inner hash by one; 
																		# Camel3 1.5.4, 9.4.3, Cookbook 5.14. 
																		# This count is different from the hits count below in that it 
																		# counts matches of individual reference text words from individual 
																		# tegories in individual positions separately. We will use this count 
																		# for the occurrence points calculation below.
																			
										} else {
										
											error( $q, "wordFormCognate is '$wordFormCognate', I'm in sub create_score");
										
										}

										++$hits;
										push @{ $position{$word} }, "$word|$workKey|$posWordRef|$posWordCur";
																				# Creates a new entry for the multidimensional hash(!) of arrays called
																				# 'position', using the current value of $word as the key and the
																				# information we have gathered about the position as the value; Camel 
																				# 4.7.2.2, Cookbook 11.2.
										push @{ $positionRef{$posWordRef} }, "$posWordCur";
																				# Creates a new entry for the multidimensional hash(!) of arrays called
																				# 'positionRef', using the current value of $posWordRef as the key and 
																				# the posWordCur variable as the value; Camel 4.7.2.2, Cookbook 11.2.
																				# This will be used later in order to delete duplicates.
										$positionCur{$posWordCur} = $posWordRef;	# Creates a lookup hash named positionCur with posWordCur as its key
																				# and posWordRef as its value; Cookbook 5.1.
										$genFreqCur{$posWordCur} = $genFreq;	# Creates a lookup hash named genFreqCur with posWordCur as its key
																				# and genFreq as its value; Cookbook 5.1. We will use this for the 
																				# position calculation below.
										$genFreqRef{$posWordRef} = $genFreq;	# Creates a lookup hash named genFreqRef with posWordRef as its key
																				# and genFreq as its value; Cookbook 5.1. We will use this for the 
																				# occurrence calculation below.
									}									# Closes the while (@values) loop; Nutshell 4.3.
								}										# Closes the if ($word =~ /$key/) block; Nutshell 4.3.
							} 											# Closes the foreach my $key (keys %inwords) loop; Nutshell 4.3.
						} else {

							if (exists($inwords{$word})) {					# Checks if $word is contained in inwords hash(!); Cookbook 4.8, 5.3,
																			# Camel4.4, Elements 8.1. The inwords hash is the lookup table created
																			# from search text user entries.
								push @matchLines, $textLineCounter;		# We will need this in order to establish a hitLine in TLG Workplace 
																		# and Pandora files.
								$chunk = "<b>$chunk</b>";					# Surrounds $chunk with HTML bold tags; Camel3 1.5.2. We highlight the
																			# word that the current text has in common with the search text.
	#							$chunk = "<span class=hilite>$chunk</span>";					# Surrounds $chunk with HTML bold tags; Camel3 1.5.2. We highlight the
																			# word that the current text has in common with the search text.
	#error( $q, "$chunk<br>");							
								my @values;									# Declares a private variable that exist only within the innermost en-
																			# closing block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
								@values = @{ $inwords{$word} };				# Puts information on $word contained in the lookup hash in the values 
																			# array; Cookbook 11.2.
								while (@values) {							# While there are any elements left in the values array, the following
																			# block of code is executed; Learning A.3. Chapter 4, Camel 1.6.2.1. As
																			# the values array may contain more than one pair of position plus fre-
																			# quency information--the word may occur at various positions in the 
																			# search text, for instance, and any match more precise than a mere 
																			# cognate yields more than one set of information -, we need to iterate
																			# through it.
									($posWordRef, $genFreq, $wordUni, $wordFormCognate) = splice(@values, 0, 4);	# Removes two elements from the values array, starting at
																			# pos. 0, and puts them in variables; Cookbook 4.11.
									if ($wordFormCognate eq "word") {

										$countMatches{$posWordRef}{word}++;	# Auto-increments the value stored under the $posWordRef key 
																		# of the outer hash and the word key of the inner hash by one; 
																		# Camel3 1.5.4, 9.4.3, Cookbook 5.14. 
																		
									} elsif ($wordFormCognate eq "form") {

										$countMatches{$posWordRef}{form}++;	# Auto-increments the value stored under the $posWordRef key 
																		# of the outer hash and the form key of the inner hash by one; 
																		# Camel3 1.5.4, 9.4.3, Cookbook 5.14. 
																		
									} elsif ($wordFormCognate eq "cognate") {

										$countMatches{$posWordRef}{cognate}++;	# Auto-increments the value stored under the $posWordRef key 
																		# of the outer hash and the cognate key of the inner hash by one; 
																		# Camel3 1.5.4, 9.4.3, Cookbook 5.14. 
																		# This count is different from the hits count below in that it 
																		# counts matches of individual reference text words from individual 
																		# tegories in individual positions separately. We will use this count 
																		# for the occurrence points calculation below.
																		
									} else {
									
										error( $q, "wordFormCognate is '$wordFormCognate', I'm in sub create_score");
									
									}

									++$hits;
									push @{ $position{$word} }, "$word|$workKey|$posWordRef|$posWordCur";
																			# Creates a new entry for the multidimensional hash(!) of arrays called
																			# 'position', using the current value of $word as the key and the
																			# information we have gathered about the position as the value; Camel 
																			# 4.7.2.2, Cookbook 11.2.
									push @{ $positionRef{$posWordRef} }, "$posWordCur";
																			# Creates a new entry for the multidimensional hash(!) of arrays called
																			# 'positionRef', using the current value of $posWordRef as the key and 
																			# the posWordCur variable as the value; Camel 4.7.2.2, Cookbook 11.2.
																			# This will be used later in order to delete duplicates.
									$positionCur{$posWordCur} = $posWordRef;	# Creates a lookup hash named positionCur with posWordCur as its key
																			# and posWordRef as its value; Cookbook 5.1.
									$genFreqCur{$posWordCur} = $genFreq;	# Creates a lookup hash named genFreqCur with posWordCur as its key
																			# and genFreq as its value; Cookbook 5.1. We will use this for the 
																			# position calculation below.
									$genFreqRef{$posWordRef} = $genFreq;	# Creates a lookup hash named genFreqRef with posWordRef as its key
																			# and genFreq as its value; Cookbook 5.1. We will use this for the 
																			# occurrence calculation below.
								}											# Closes the while (@values) loop; Nutshell 4.3.
							}												# Closes the if ($inwords{$word}) block; Nutshell 4.3.
						}												# Closes the if ($mt eq "pt") ... else ... block; Nutshell 4.3.
					}													# Closes the foreach $chunk (@wordsLine) loop; Nutshell 4.3.

#					push(@newText, @wordsLine);							# Cookbook 4.9.
					$newLine = "@wordsLine";							# Turns the (changed) wordsLine array into a string of its elements and
																		# stores it in the newline variable; Camel3 2.6.5, Cookbook 4.2, Lear-
																		# ning 2.3.2.
#error( $q, $matchedWords ) unless ($matchedWords eq "the matched words are: ");
#					print "$newLine<br>";
					push (@newText, $newLine);							# Appends the newline variable as a new element to the newText array; 
																		# Cookbook 4.9.
				}														# Closes the foreach $line loop; Nutshell 4.3.
				@text = ();												# Empties the @text array; Learning 3.2, Camel 2.3.4.

#				print "<br>position hash:<br>";										# For debugging; Cookbook 11.11. 
#				print Dumper(\%position);											# For debugging; Cookbook 11.11. 
	#			print "<p>Total words in this text: $posWordCur</p>";				# For debugging.
	#			print "<p>Sum of word hits in this text: $hits</p>";				# For debugging.

				if ($hits < 2) {										# If the value stored in the hits variable is less than 2, the follow-
																		# ing block of code is executed; Learning 1.5.3, 2.4.2. This avoids
																		# division by zero and operations which cause an "uninitialized value" 
																		# error message in case there are fewer than two hits; Medinets ch5, 
#					print "<p>There are fewer than 2 hits in this text.</p>";	# 11, 16.
					@newText = ();										# Empties the @newText array; Learning 3.2, Camel 2.3.4.
					@matchLines = ();									# Empties the @matchLines array; Learning 3.2, Camel 2.3.4.
					$fileLineCounter = 0;
					$matchedWords = "";									# For debugging
					next LINE;												# Skips to the end of the current while (<FH>) loop iteration and 
																		# starts the next iteration; Camel3 1.6.2.4. 
				}														# Closes the if ($hits < 2) block; Nutshell 4.3.
				
				if (keys %countMatches < 2) {							# If the countMatches hash has fewer than 2 keys, the following block of
																		# code is executed; Learning 2.3, Camel 3.2.79, 3.2.84. The number of
																		# keys of this hash equals the number of search text words matched. If 
																		# there is only one of them, we skip this text in order to save 
#					print "<p>There are matches for fewer than 2 search text words.</p>";	# time.
					@newText = ();										# Empties the @newText array; Learning 3.2, Camel 2.3.4.
					@matchLines = ();									# Empties the @matchLines array; Learning 3.2, Camel 2.3.4.
					$fileLineCounter = 0;
					$matchedWords = "";									# For debugging
					next LINE;												# Skips to the end of the current while (<FH>) loop iteration and 
																		# starts the next iteration; Camel3 1.6.2.4. 
				}

				# The following code eliminates the duplicates in the collection of matched words. We usually have duplicates here, since any 
				# match more precise than a mere cognate yields more than one set of information. While we will need those duplicates for the 
				# occurrence calculations later on, we eliminate them here in order to speed up the density and position calculations.
				
				while (($posWordRef, @anyPosWordCur) = each (%positionRef)) {	# While there are any $posWordRef keys and @anyPosWordCur 
																		# values left, the following block of code is executed for each entry
																		# in the hash of arrays called positionRef; Cookbook 5.4, Camel 8.3.2.
#					print "<br>$posWordRef: @{$positionRef{$posWordRef}}\n";	# For debugging.

					my @uniqPosWordCur;									# Declares a private variable that exists only within the innermost en-
																		# closing block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
																			
					@anyPosWordCur = @{ $positionRef{$posWordRef} };	# Puts information on $posWordRef contained in positionRef hash in   
																		# anyPosWordCur array; Cookbook 11.2.
					foreach $posWordCur (@anyPosWordCur) {				# For each posWordCur value stored in the anyPosWordCur array, the
																		# following block of code is processed; Cookbook 4.6.
						push(@uniqPosWordCur, $posWordCur) unless $seen{$posWordCur}++;	# Stores the posWordCur value in the uniqPosWordCur
																		# array unless it is already stored in the seen hash, and then
																		# stores it there, too; Cookbook 4.6.
					}													# Closes the foreach $posWordCur block; Nutshell 4.3.
#					print "<br>uniqPosWordCur: @uniqPosWordCur";
					push @multiPosWordCur, [ @uniqPosWordCur ];			# Adds the uniqPosWordCur array to the multidimensional 
																		# multiPosWordCur array; Camel 4.6.2. This will be used to 
																		# calculate the center of the quotation later on.
				}														# Closes the while loop; Nutshell 4.3.


				# The following blocks of code determine the anchor or core of the matched word sequence. Tests have shown that the best way
				# to determine the core of a quotation/allusion is to determine where in the current text the position of the matched words re-
				# lative to each other most resembles the relative position of these words in the search text. Now that the whole text file has
				# been searched for matches with our lookup hash and all those matches have been stored in the position hash, we can loop 
				# through all elements stored for each word in order to calculate the score for its position, repeating this process with every
				# matched position in the current text acting as the core in order to see where we get the highest number of position points. 
				# This is where we will locate the anchor or core of the quotation.
				# We need the position calculation, because our goal is to score texts based on, among other things, the degree to which the 
				# sequence of the words they have in common with our search text matches their sequence in the search text. And we need to know
				# the core of the quotation for the density calculation later on, as this is the only way for the software to know which among
				# several matches for the same search text position to pick when it should measure the gaps.


				for $i ( 0 .. $#multiPosWordCur ) {						# For every row of the array of arrays named multiPosWordCur, the fol-
																		# lowing block of code is executed; Camel3 3.1.3.
					for $j ( 0 .. $#{$multiPosWordCur[$i]} ) {			# For every column of the array of arrays named multiPosWordCur, the 
																		# following block of code is executed; Camel3 3.1.3. We consider every 
																		# position of a matched word to be possibly the core of the quotation
																		# in the current text.
						$corePosWordCur = $multiPosWordCur[$i][$j];		# The value stored in row i and column j of the array of arrays named
																		# multiPosWordCur is stored in the variable named corePosWordCur; Ca-
																		# mel3 3.1.3.

						$sumPointsPos = 0;								# We need to reset the value for sumPointsPos as we find out how many 
																		# position points we would get if the current value of the corePosWord-
																		# Cur actually represented the core of the quotation.
						%points = ();
						%allMovePos = ();
						
						
						$corePosWordRef = $positionCur{$corePosWordCur};			# Gets the value associated with the key stored in the corePosWordCur-
																				# variable in the positionCur lookup hash and puts 
																				# it in the corePosWordRef variable; Learning 1.5.6, 
																				# Nutshell 4.2.4.2.
						for $word ( keys %position ) {					# For every key of the hash named position, the following block of code 
																		# is executed with the key stored in the word variable; Camel3 9.2.3.
							my ($oldPosWordRef, $oldPosWordCur);
							my ($relPosWordRef, $relPosWordCur);
		
#							print "<br>$word: @{ $position{$word} }\n";			# For debugging.
							@dataPerWord = @{ $position{$word} };				# Puts information on $word contained in position hash in dataPerWord 
																				# array; Cookbook 11.2.
							while (@dataPerWord) {								# As the dataPerWord array may contain more than one set of information
																				# --the word may occur at various positions in the current text, and 
																				# any match more precise than a mere cognate yields more than one set  
																				# of information -, we need to iterate through it; Learning A.3. Chap-
																				# ter 4, Camel 1.6.2.1.
								my $data = shift(@dataPerWord);						# Removes the first element of the dataPerWord array and stores it in 
																				# the $data variable; Learning 3.4.4.
		
								($word, $workKey, $posWordRef, $posWordCur) = split (/\|/, $data);	# Splits the element stored in the $_ variable at the 
																				# | record separator and puts the values in the variables 
																				# in brackets; Camel 3.2.155.			
		
								unless ($posWordRef == $oldPosWordRef and $posWordCur == $oldPosWordCur) {	# Unless the word positions in both the 
																				# search and the current text are the same as for the previous element 
																				# (or there are no previously stored positions), the following block is
																				# executed; Learning 2.4.2, 4.2. GEHT DAS SO???????????????
																				# This occurs when there is more than one set of information on the
																				# same match as the match was better than just a cognate match.
									unless ($posWordRef == $oldPosWordRef) {	# Unless the word position in the search text is the same as for the
																				# previous element (or there is no previously stored position), this 
										$relPosWordRef = $posWordRef - $corePosWordRef;	# block calculates the position of the word in the search text 
									}											# in relation to the core position of matched words in the search
																				# text; Learning 2.6.1.
									unless ($posWordCur == $oldPosWordCur) {	# Unless the word position in the current text is the same as for the 
																				# previous element (or there is no previously stored position), this 
										$relPosWordCur = $posWordCur - $corePosWordCur;	# block calculates the position of the word in the current text
									}											# in relation to the core position of matched words in the current
																				# text; Learning 2.6.1.
									$movePos = $relPosWordCur - $relPosWordRef;	# Calculates the points which the word scores for its position by com-
																				# paring the position relative to the average position in the current 
																				# text on the one hand and the search text on the other hand; Learning 
																				# 2.6.1.
									if ($movePos < 0) {							# Checks if value for points is negative--this occurs when matched 
																				# word occurs earlier in current text than in search text; Learning
																				# 4.2.
										$movePos = -$movePos + 1;				# Turns the negative value for points positive by putting a minus mark
																				# in front of it, and adds a penalty point for reversing the sequence;
									}											# Dummies 6.3, Learning 2.6.
			#						if ("$movePos < $bestMovePos") {			# If the value stored in the movePos variable is lower than that stored
			#																	# in bestMovePos (or if nothing is stored in bestMovePos yet), the 
			#							$bestMovePos = $movePos;				# value of movePos is transferred to bestMovePos; Learning 2.4.2. A 
			#						}											# higher value for movePos means the word is farther away
																				# from the search position.
																				# I HAVE GIVEN UP THIS TECHNIQUE AS IT IS COMPLICATED TO KEEP DIFFE-
																				# RENT BESTMOVEPOS VALUES FOR DIFFERENT REFERENCE POSITIONS THIS
																				# WAY (WHEN A WORD OCCURS MORE THAN ONCE IN THE REFERENCE TEXT, WE
																				# WANT TO FIND THE BEST POSITION IN THE CURRENT TEXT FOR EACH OCCUR-
																				# RENCE IN THE REFERENCE TEXT). I GUESS IT COULD BE DONE WITH A NUM-
																				# BER OF IF/ELSIF BLOCKS, BUT THE FOLLOWING TECHNIQUE SEEMED EASIER
																				# TO IMPLEMENT:
#									print "<br><br>corePosWordRef: $corePosWordRef";	# For debugging.
#									print "<br>oldPosWordRef: $oldPosWordRef";			# For debugging.
#									print "<br>posWordRef: $posWordRef";				# For debugging.
#									print "<br>relPosWordRef: $relPosWordRef";			# For debugging.
#									print "<br><br>corePosWordCur: $corePosWordCur";	# For debugging.
#									print "<br>oldPosWordCur: $oldPosWordCur";			# For debugging.
#									print "<br>posWordCur: $posWordCur";				# For debugging.
#									print "<br>relPosWordCur: $relPosWordCur";			# For debugging.
#									print "<br>movePos: $movePos";						# For debugging.

		#							push(@{$allMovePos{$posWordRef}}, $movePos);	# Stores the movePos value in the allMovePos hash, using the posi-
									$allMovePos{$posWordRef}{$posWordCur} = "$movePos";
																				# tion of the word in the search text as the key; Camel 4.7.2.2, Cook-
																				# book 11.2. This allows us to find the best movePos value for eve-
																				# ry search text position later on.
									$oldPosWordRef = $posWordRef;				# Puts the current values for posWordRef and posWordCur in "old" va-
									$oldPosWordCur = $posWordCur;				# riables so that in the next iteration through the loop, new values
																				# can be checked against the old--if they are the same, many blocks
																				# can be skipped, which is time efficient; Camel 8.3.1.
								}												# Closes the unless block; Nutshell 4.3.
							}													# Closes the while (@dataPerWord) loop; Nutshell 4.3.
#							print '<br>allMovePos hash:<br>';					# For debugging.
#							print Dumper(\%allMovePos);							# For debugging. Being done with every iteration of the foreach loop,
																				# which allows for controlling the growth of the hash.
						}														# Closes foreach $word / while $word loop; Nutshell 4.3.
		
						# The following block of code establishes the number of points we would award for the positions of the matched words in
						# the current text if the current value of the corePosWordCur variable represented the core of the quotation in the 
						# current text. It does so by traversing the allMovePos hash to look for the best movePos value at each search text position.
						
						for $posWordRef ( keys %allMovePos ) {					# Camel3 9.2.3.
		
							my @sortedPosCurPerPosRef;							# Declares private variables that exist only within the innermost en-
							my ($bestPosCurPerPosRef, $bestMovePosPerPosRef);
							my $pointsPos = 3;									# This is going to be the pointsPos value if bestMovePosPerPosRef = 
																				# 0. This is the case whenever the relative position of the word in 
																				# question is exactly the same in the current and the search text.
							
							@sortedPosCurPerPosRef = sort { $allMovePos{$posWordRef}{$a} <=> $allMovePos{$posWordRef}{$b} } keys %{ $allMovePos{$posWordRef} };
																				# Sorts the allMovePos hash of hashes by the values of the inner hash 
																				# and stores the corresponding keys in the sortedPosCurPerPosRef
																				# array; Cookbook 5.9, Camel3 9.4.3. We need to find the smallest  
																				# move value for any match in the current text.
		
							$bestPosCurPerPosRef = shift(@sortedPosCurPerPosRef);	# Removes the first (= best) posWordCur value from the sortedPosCur-
																				# PerPosRef hash and stores it in the bestPosCurPerPosRef variable; 
																				# Learning 3.4.4.
							
#							push @listPosWordCur, $bestPosCurPerPosRef;			# Camel3 29.2.116. We will need this for the density calculation below.
							push(@{$allListsPosWordCur{$corePosWordCur}}, $bestPosCurPerPosRef);	# Camel3 9.2.2. We will need this for the 
																		# density calculation below.
							
							$bestMovePosPerPosRef = $allMovePos{$posWordRef}{$bestPosCurPerPosRef};	# Cookbook 5.4.
							
		#					print "<br>posWordRef is $posWordRef, bestPosCurPerPosRef is $bestPosCurPerPosRef, bestMovePosPerPosRef is $bestMovePosPerPosRef";
		
							$pointsPos = 1 / $bestMovePosPerPosRef if ($bestMovePosPerPosRef > 0);	# Divides 1 by the value stored in the best-
																				# MovePosPerWordRef variable if the latter is more than 0, and stores
																				# the results in the pointsPos variable; Learning 2.6, Camel3 3.7.
							$sumPointsPos += $pointsPos;						# Adds up the points for position values for every search word found in
																				# the current text; Learning 2.6.1.
							push(@{$points{$posWordRef}}, "bestPosCurPerPosRef: \t $bestPosCurPerPosRef");	# For debugging.
							push(@{$points{$posWordRef}}, "bestMovePosPerPosRef: \t $bestMovePosPerPosRef");	# For debugging.
							push(@{$points{$posWordRef}}, "Points Position: \t\t\t $pointsPos");
							push(@{$points{$posWordRef}}, "Sum Points Position: \t\t $sumPointsPos");
		
						}														# Closes the while loop; Nutshell 4.3.
						$sumPointsPos = $sumPointsPos - 3;						# We decrease sumPointsPos by 3 as the central word of the quotation 
																				# has a move value of 0 by definition and therefore gets 3 points un-
																				# merited.
						$allSumsPointsPos{$corePosWordCur} = $sumPointsPos;	# Creates a new entry in the allSumsPointsPos hash, with the core-
																		# PosWordCur variable as the key and the sumPointsPos variable as the
																		# value; Cookbook 5.1. We store the number of position points the cur-
																		# rent text would get if the current value of corePosWordCur actually 
																		# represented the core position of the quotation.
#						print "<br>points hash if core at $corePosWordCur:<br>";
#						print Dumper(\%points);									# For debugging; Cookbook 11.11, Camel 4.2.1.
#						print "<br>points hash if core at $corePosWordCur:<br>" if $workKey =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;
#						print Dumper(\%points) if $workKey =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;									# For debugging; Cookbook 11.11, Camel 4.2.1.
					}
				}

				# We now sort the allSumsPointsPos hash based on its values. The key that corresponds to the highest position points value in-
				# dicates the core of the quotation in the current text. As a perfect quotation has the same position points value for every 
				# one of its words, we need to establish the bestSumsPointsPos hash and sort it, too. (We can't leave it up to the program's 
				# array to make the choice between them, as the duplicate text removing below depends on the same corePosWordCur and coreLine 
				# being chosen every time.)
				
				@sortedSumsPointsPos = sort { $allSumsPointsPos{$b} <=> $allSumsPointsPos{$a} } keys %allSumsPointsPos;	# Cookbook 5.9.
				my (%bestSumsPointsPos, $oldSumPoints);
				foreach my $sumPointsPos (@sortedSumsPointsPos) {
					my $sumPoints = $allSumsPointsPos{$sumPointsPos};
#error( $q, "sumPoints is $sumPoints<br>sortedSumsPointsPos is @sortedSumsPointsPos" ) if $workKey =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;					
					last if $sumPoints < $oldSumPoints;				# We exit the loop as soon as soon as we see a lower sumPoints value
					$bestSumsPointsPos{$sumPointsPos} = $sumPoints;
					$oldSumPoints = $sumPoints;
				}
				my @sortedBestSumsPointsPos = sort keys %bestSumsPointsPos;	# Cookbook 5.9.
#				$corePosWordCur = pop @sortedSumsPointsPos;
				$corePosWordCur = shift @sortedBestSumsPointsPos;
#error( $q, "corePosWordCur is $corePosWordCur<br>sortedBestSumsPointsPos is @sortedBestSumsPointsPos" ) if $workKey =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;					
##				print "<br>corePosWordCur is $corePosWordCur" if $corePosWordCur;

				# Now that we have the word position at the quotation core in the current text, we get the corresponding word position in the 
				# search text, the position points, and the list of best matches for each reference text position in the current text.
				
				$corePosWordRef = $positionCur{$corePosWordCur};		# Gets the value associated with the key stored in the corePosWordCur-
																		# variable in the positionCur lookup hash and puts it in the corePos-
																		# WordRef variable; Learning 1.5.6, Nutshell 4.2.4.2.
#				print "<br>corePosWordRef is $corePosWordRef" if $corePosWordRef;

				$sumPointsPos = $allSumsPointsPos{$corePosWordCur};
#				print "<br>sumPointsPos is $sumPointsPos" if $sumPointsPos;
				
				@listPosWordCur = @{$allListsPosWordCur{$corePosWordCur}};
#				print "<br>listPosWordCur is @listPosWordCur" if @listPosWordCur;


				# We go through all search text words that we have a match for in the current text and add up their general frequency values.
				# Then we derive relative frequency values from the total. We do this so that the weighting of the frequency aspect will be 
				# the same regardless of the size of the text database (TLG, CLCLT) being searched.
				
				foreach $posWordRef (keys %genFreqRef) {
				
					$genFreqTotal += $genFreqRef{$posWordRef};
					
				}
				
				foreach $posWordRef (keys %genFreqRef) {
				
					$relFreq = ( $genFreqRef{$posWordRef} / $genFreqTotal );
#					print "<br>relFreq is $relFreq";	# For debugging.
					$relFreqRef{$posWordRef} = $relFreq;
					
				}
				
				foreach $posWordCur (keys %genFreqCur) {
				
					$relFreq = ( $genFreqCur{$posWordCur} / $genFreqTotal );
#					print "<br>relFreq is $relFreq";	# For debugging.
					
				}
				
				
				# The following chunk of the program calculates the number of points we award the current text for the occurrence of search
				# text words. It does so by taking quantity (number of hits), quality (exact word, form of word, or form of cognate), and
				# rareness of the matched words into account.
				
				foreach $posWordRef (keys %countMatches) {
				
					my $occWord;
					
					my $countMatchWord = $countMatches{$posWordRef}{word}; 
					my $countMatchForm = $countMatches{$posWordRef}{form}; 
					my $countMatchCognate = $countMatches{$posWordRef}{cognate}; 
					
					$relFreq = $relFreqRef{$posWordRef};

#						push(@{$points{$posWordRef}}, "\tcountMatch is $countMatch");			# For debugging; Camel 4.7.2.2, Cookbook 11.2.
#						push(@{$points{$posWordRef}}, "\trelFreq is $relFreq");			# For debugging; Camel 4.7.2.2, Cookbook 11.2.

					# The following loops add up occurrence points for the current posWordRef. A word brings in 3 points divided by the number 
					# of the match each time it is matched. A form brings in 2 points divided by the number of the match each time it is 
					# matched. A cognate brings in 1 point divided by the number of the match each time it is matched. The division operation is
					# done so that repeated occurrences of the same word/form/cognate result in a lower number of points than the occurrence of 
					# different words/forms/cognates of the search text. Otherwise, a text that contains the same string several dozen times, 
					# such as a lexicon, would get too many points.
					
					for (my $i = 1; $i <= $countMatchWord; $i++) {		# For every value stored in the $1 variable, i.e. from 1 to the num-
																		# ber stored in the countMatchWord variable, the following block of code
																		# is executed; Camel3 4.4.2.
						$occWord += (3 / $i);							# Divides 1 by the number stored in the i counter variable and
																		# adds the result to the number stored in the occWord variable; Ca-
																		# mel3 1.5.3. 
#						push(@{$points{$posWordRef}}, "\t\toccWord is $occWord");			# For debugging; Camel 4.7.2.2, Cookbook 11.2.
					} 
					
					for (my $i = 1; $i <= $countMatchForm; $i++) {		# For every value stored in the $1 variable, i.e. from 1 to the num-
																		# ber stored in the countMatchForm variable, the following block of code
																		# is executed; Camel3 4.4.2.
						$occWord += (2 / $i);							# Divides 1 by the number stored in the i counter variable and
																		# adds the result to the number stored in the occWord variable; Ca-
																		# mel3 1.5.3. 
#						push(@{$points{$posWordRef}}, "\t\toccWord is $occWord");			# For debugging; Camel 4.7.2.2, Cookbook 11.2.
					} 
					
					for (my $i = 1; $i <= $countMatchCognate; $i++) {	# For every value stored in the $1 variable, i.e. from 1 to the num-
																		# ber stored in the countMatchCognate variable, the following block of code
																		# is executed; Camel3 4.4.2.
						$occWord += (1 / $i);							# Divides 1 by the number stored in the i counter variable and
																		# adds the result to the number stored in the occWord variable; Ca-
																		# mel3 1.5.3. 
#						push(@{$points{$posWordRef}}, "\t\toccWord is $occWord");			# For debugging; Camel 4.7.2.2, Cookbook 11.2.
					} 
					
					my $pointsOcc = $occWord * (1 - $relFreq);			# Subtracts the relFreq value from one, multiplies the result by the 
																		# occWord value, and stores the result in pointsOcc;; Learning 2.6.1, 
																		# Cookbook 5.1, Nutshell 4.5.6. We do this in order to move texts con-
																		# taining matches of rare words up in the ranking.
					$sumPointsOcc += $pointsOcc;					# Adds up the points for occurrence values for every search word found 
																	# in the current text; Learning 2.6.1.
#						push(@{$points{$posWordRef}}, "\tpointsOcc is $pointsOcc");			# For debugging; Camel 4.7.2.2, Cookbook 11.2.
#						push(@{$points{$posWordRef}}, "\tsumPointsOcc is $sumPointsOcc");			# For debugging; Camel 4.7.2.2, Cookbook 11.2.
				}
#				print "<br>points hash:<br>";							# For debugging; Cookbook 11.11, Camel 4.2.1.
#				print Dumper(\%points);									# For debugging; Cookbook 11.11, Camel 4.2.1.
					
				
				# The following chunk of the program calculates the density of matched words in the current text. It does so by calculating the 
				# gap between every matched word and giving more points for smaller gaps. The goal is to give a text with good matches, say, 
				# for search words #24, #25, and #26 a higher score than a text with good matches for #1, #25, and #50. Also, we only award points
				# once for every match of a search text word in a given position, because otherwise, a text containing the same string dozens of 
				# times tightly packed, such as a lexicon, would get far too many points.

				my (@gaps, @sortedGaps, $gap, $smallestGap, $gapCounter);
				
				@sortedPosWordCur = sort { $a <=> $b } @listPosWordCur;	# Sorts the listPosWordCur array in numerical order; Cookbook 4.14.
#				print "<br>sortedPosWordCur: @sortedPosWordCur";
				
				while (@sortedPosWordCur) {								# While there are any elements left in the sortedPosWordCur array,
																		# the following block of code is executed; Camel 1.6.2.1.
					$highestPosWordCur = pop(@sortedPosWordCur);		# Removes the last (highest) element of the sortedPosWordCur array
																		# and puts it in the highestPosWordCur variable; Learning 3.4.3.
					foreach $posWordCur (@sortedPosWordCur) {			# For each posWordCur variable stored in the sortedPosWordCur array,
																		# the following block of code is executed; Cookbook 4.4.
						$gapPosWordCur = $highestPosWordCur - $posWordCur;	# Subtracts the current value of posWordCur from highestPosWordCur
																		# and puts the results in the gapPosWordCur variable; Learning 2.6.
#						print "<li>$highestPosWordCur : highestPosWordCur<br>";	# For debugging.
#						print "<li>$posWordCur : posWordCur<br>";			# For debugging.
#						print "<li>$gapPosWordCur : gapPosWordCur<br>";		# For debugging.
						
						$pointsDens += (1 / $gapPosWordCur) if ($gapPosWordCur > 0);	# Divides 1 by the value stored in gapPosWordCur and 
																		# adds the results to the pointsDens variable, as long as gapPosWordCur 
																		# isn't 0; Learning 2.4.2, 2.6.1, Camel 2.6.1, 8.3.
					}													# Closes the foreach $posWordCur block; Nutshell 4.3.
				}														# Closes the while (@sortedPosWordCur) block; Nutshell 4.3.
				
				
				$sumPointsOcc = $sumPointsOcc / 3;					# Divides sumPointsOcc by 3 and multiplies pointsDens by 2; Learning 2.6.
				$pointsDens = $pointsDens * 2;							# This is arbitrary, of course; the figures were chosen because in my
																		# view, the best quotations really did end up at the top of the list
																		# that way.
				$pointsTotal = $sumPointsOcc + $sumPointsPos + $pointsDens;	# Adds up the values of sumPointsOcc, sumPointsPos, and pointsDens,
																		# and puts the results in the pointsTotal variable; Learning 2.6.

				if ($pointsTotal < 1) {									# If the value stored in the pointsTotal variable is less than 1, the
																		# following block of code is executed; Camel3 3.11.
#					print "<p>The total is less than 1 point.</p>";		# For debugging.
					@newText = ();										# Empties the @newText array; Learning 3.2, Camel 2.3.4.
					@matchLines = ();									# Empties the @matchLines array; Learning 3.2, Camel 2.3.4.
					$fileLineCounter = 0;
					$matchedWords = "";									# For debugging
					next LINE;												# Skips to the end of the current loop iteration, and start the next 
																		# iteration; Camel3 1.6.2.4. 
				}														# Closes the if block; Nutshell 4.3.
					

				$posWordCur = 0;
				my %listPosWordCur;
				for (@listPosWordCur) {									# Constructs a listPosWordCur hash; Camel3 24.2.1. Hash lookups are
					$listPosWordCur{$_}++;								# faster than checking to see if arrays contain a particular element.
				}														# @listPosWordCur ist the list of best matches for each reference text 
																		# position in the current text.
				my $newTextLineCounter;
				foreach my $newLine (@newText) {
					
					++$newTextLineCounter;										# Autoincrement
					
					$newLine =~ s/<b><b><b>/<b>/g;					# Reduces triple and double tags to single tags. These occur when a 
					$newLine =~ s/<b><b>/<b>/g;						# word is more than a mere cognate match.
					$newLine =~ s/<\/b><\/b><\/b>/<\/b>/g;
					$newLine =~ s/<\/b><\/b>/<\/b>/g;

					@wordsLine = split(/\s+/, $newLine);			# Splits the content of the newLine variable at whitespace (1 or more) and
																	# puts the results in the wordsLine array; Learning 7.6.1, Cookbook 8.3.

#						if ($line =~ /\s(\S+?)-$/) {					# If the value stored in the line variable contains the pattern be-
#																		# tween the slashes, the following block of code is executed; Camel3
#																		# 5.6.2. We need to remove hyphenated words here as we did above, be-
#																		# cause otherwise the word count would not match. QUATSCH, WIR HABEN 
#																		# DIE GETRENNTEN WÖRTER JA VEREINT.
#							pop @wordsLine;								# Removes the last element of the wordsLine array; Camel3 29.2.111.
#						}

					foreach $chunk (@wordsLine) {					# Iterates over every element of the wordsLine array; Camel 2.6.4.3.
																	# The advantage of this method over a while loop is that if you change
																	# an element of the array within the foreach loop, it actually gets
																	# changed in the array itself. 
						$posWordCur += 1 if ($chunk =~ m/\w/);		# Increases the posWordCur counter by one if $chunk contains a word
																	# character; Learning 2.6.1.
						$coreLineCur = $newTextLineCounter if $posWordCur == $corePosWordCur;	# The line that contains corePosWordCur is the line that
																		# contains the core of the quotation in the current text. 
#						error( $q, "coreLineCur is $coreLineCur, hitLine is $hitLine" ) unless $coreLineCur eq "";	# For debugging
#						error( $q, "coreLineCur is $coreLineCur, hitLine is $hitLine, corePosWordRef is $corePosWordRef" ) if ($workKey =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/ and $coreLineCur);	# For debugging
#error( $q, "coreLineCur is $coreLineCur, hitLine is $hitLine, corePosWordRef is $corePosWordRef" ) if ($workKey =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/ and $coreLineCur);	# For debugging
						
						if ( $listPosWordCur{$posWordCur} and $chunk =~ /<b>/ ) {
						
							$chunk =~ s/<b>/<span class=corematch>/;
							$chunk =~ s/<\/b>/<\/span>/;
							
						} elsif ( $chunk =~ /<b>/ ) {
						
							$chunk =~ s/<b>/<span class=match>/;
							$chunk =~ s/<\/b>/<\/span>/;
							
						} elsif ( $listPosWordCur{$posWordCur} and $chunk =~ m/\w/) {
						
							error( $q, "The following word is in the best matches list, but it doesn't have a bold tag:<br>newLine is '$newLine'<br>posWordCur is $posWordCur<br>chunk is '$chunk'<br>listPosWordCur is @listPosWordCur" );
							
						}
					}

					$newLine = "@wordsLine";						# Turns the (changed) wordsLine array into a string of its elements and
																	# stores it in the newline variable; Camel3 2.6.5, Cookbook 4.2, Lear-
																	# ning 2.3.2.
					
					$newLine = "      $newLine<br>\n" if $fo eq "CLCLT";
				}
				
				if ($fo ne "CLCLT") {
				
#					$work = process_work_title($work);					# Calls the process_work_title subroutine, passes it the work va-
																		# riable, and then passes the result of the subroutine back to the
																		# work variable; Camel3 6.2.1. Deals with Beta code formatting 
																		# characters and Greek in work titles.
					
					## The next block of code establishes the number of the line containing the hit exported from the TLG. This code is only
					## guaranteed to work correctly if the same number of lines before and after the hit were exported.
					
					my ($matchLineNumber, $gapLineNumbers, %gapsLineNumbers, @sortedMatchLineNumbers);
					my $allGapLineNumbers;			# for debugging
					
					my $numberOfLines = scalar @newText;
					
					my $middleLineNumber = $numberOfLines / 2;
					
#					error( $q, "matchedWords is $matchedWords<br>matchLines is @matchLines" );
					
					foreach $matchLineNumber (@matchLines) {
					
						if ($matchLineNumber < $middleLineNumber) {
							$gapLineNumbers = $middleLineNumber - $matchLineNumber;
						} else {
							$gapLineNumbers = $matchLineNumber - $middleLineNumber;
						}
						$gapsLineNumbers{$matchLineNumber} = $gapLineNumbers;
#						$allGapLineNumbers .= "<br>matchLineNumber is $matchLineNumber, gapLineNumbers is $gapLineNumbers";	# For debugging
						
					}
					
					foreach $matchLineNumber (sort { $gapsLineNumbers{$a} <=> $gapsLineNumbers{$b} } keys %gapsLineNumbers) {
																		# Cookbook 5.9.
						push @sortedMatchLineNumbers, $matchLineNumber;

					}
					
#					error( $q, "numberOfLines is $numberOfLines<br>middleLineNumber is $middleLineNumber<br>allGapLineNumbers: $allGapLineNumbers<br>matchedWords is $matchedWords<br>matchLines is @matchLines<br>sortedMatchLineNumbers is @sortedMatchLineNumbers" );
					
					$hitLine = shift(@sortedMatchLineNumbers);
					
					
					foreach my $newLine (@newText) {
						
						my $newestLine;
						
						my @chunks = split /(&.*?\$)/, $newLine;
						
						foreach my $chunk (@chunks) {
							if ($chunk =~ /&`?(.*)\$/) {
								$newestLine .= $1; 
							}
							else {
								$chunk = convert_string_to_unicode($chunk);	# Calls the convert_string_to_unicode subroutine, passes it the chunk va-
																		# riable, and then passes the result of the subroutine back to the
																		# chunk variable; Camel3 6.2.1.
								$newestLine .= $chunk; 
							}
						}
						
						$newLine = "      $newestLine<br>\n";						# Adds an HTML line break tag at the end of the string stored in the 
																		# newline variable; Camel3 3.8. This maintains Cetedoc line breaks.
					}
				}
								
				
				$mldb = tie %score, 'MLDBM', $mldbScoreFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file: mldbScoreFile is $mldbScoreFile $!" );
																		# Associates the database file whose path is stored in the mldbScore-
																		# File variable with the score hash so that, 
																		# using the MLDBM module, any changes to the hash are saved to 
																		# the file (which is created with write access for us but no one else 
																		# in case it doesn't exist yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 
																		# (32), 2.9 (51), Cozens 435.
				$dbWork = tie %scoreWork, 'DB_File', $dbScoreWorkFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File file: dbScoreWorkFile is $dbScoreWorkFile $!" );
				my $dbTotal = tie %scoreTotal, 'DB_File', $dbScoreTotalFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File file: dbScoreTotalFile is $dbScoreTotalFile $!" );
				undef $mldb;											# Frees up the memory associated with the objects; Camel3 29.2.187, 
				undef $dbWork;											# Cookbook 11.0.
				undef $dbTotal;

				
				## The following block of code keeps duplicate texts away from the score hash. This is done by checking to see if the text's 
				## hash keys are the same, apart from the numbers. If so, we check to see if the text is largely the same, and if the quotation
				## core is the same. If this is the case, only the one whose title is more likely to coincide with the quotation core is main-
				## tained. (It would be odd if we had highlighted, say, verse 52 as the core, but the work title read "Verse 46.")
				
#				my $currentKey = $workKey;
#				$currentKey =~ s/\d//g;									# Removes digits from $currentKey.
				# Solution above fails when there is a letter after a page or paragraph number. Solution below retains title up to the first 
				# letter encountered. We accept the risk that if a digit occurs early on in a book title, not much of it remains, if anything... 
				# which means that the decision whether we have a duplicate is based mainly on the text in this case, as currentKeys tend 
				# toward being identical.
				my @currentKeyChunks = split /\d+/, $workKey;			# Camel3 29.2.161
				my $currentKey = shift @currentKeyChunks;				# Camel3 29.2.149
				
				my %linesSeen = ();										# Cookbook 4.7. lookup table to test membership of @originalText
				my $numberLinesOriginalText = scalar @originalText;
				my $gapHitLineCoreLineCur;
				if ($coreLineCur < $hitLine) {
					$gapHitLineCoreLineCur = $hitLine - $coreLineCur;
				} else {
					$gapHitLineCoreLineCur = $coreLineCur - $hitLine;
				}
				
				foreach my $line (@originalText) { $linesSeen{$line} = 1 }	# build lookup table
				
				foreach my $key (keys %scoreWork) {						# Cookbook 5.4.
					
					my @scoreOnly = ();									# answer
#					my $scoreKey = $key;
#					$scoreKey =~ s/\d//g;								# Removes digits from $scoreKey.
					# Solution above fails when there is a letter after a page or paragraph number. Solution below retains title up to the first 
					# letter encountered. We accept the risk that if a digit occurs early on in a book title, not much of it remains, if anything... 
					# which means that the decision whether we have a duplicate is based mainly on the text in this case, as currentKeys tend 
					# toward being identical.
					my @scoreKeyChunks = split /\d+/,  $key;			# Camel3 29.2.161
					my $scoreKey = shift @scoreKeyChunks;				# Camel3 29.2.149
					
					if ($currentKey eq $scoreKey) {
		
						my @scoreOriginalText = @{ $score{$key}{'originalText'} };
						
						foreach $line (@scoreOriginalText) {			# find only elements in @A and not in @B
							unless ($linesSeen{$line}) {
								push(@scoreOnly, $line);				# it's not in %linesSeen, so add to @scoreOnly
							}
						}
						my $numberLinesScoreOriginalText = scalar @scoreOriginalText;
						my $numberLinesText;
						if ($numberLinesScoreOriginalText < $numberLinesOriginalText) {
							$numberLinesText = $numberLinesScoreOriginalText;
						} else {
							$numberLinesText = $numberLinesOriginalText;
						}
						my $numberLinesScoreOnly = scalar @scoreOnly;
#error( $q, "workKey is $workKey<br>\nkey is $key<br>\numberLinesText is $numberLinesText<br>\nnumberLinesScoreOnly is $numberLinesScoreOnly<br>\ngapHitLineCoreLineCur is $gapHitLineCoreLineCur<br>\ncoreLineCur is $coreLineCur<br>\nscoreOnly is<br>\n@scoreOnly<br>\nscoreOriginalText is<br>\n@scoreOriginalText<br>\noriginalText is<br>\n@originalText<br>" ) if $workKey =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;
#error( $q, "workKey is $workKey<br>\nkey is $key<br>\numberLinesText is $numberLinesText<br>\nnumberLinesScoreOnly is $numberLinesScoreOnly<br>\ngapHitLineCoreLineCur is $gapHitLineCoreLineCur<br>\ncoreLineCur is $coreLineCur<br>\nscoreOnly is<br>\n@scoreOnly<br>\nscoreOriginalText is<br>\n@scoreOriginalText<br>\noriginalText is<br>\n@originalText<br>" );
						
#						if ($numberLinesScoreOnly < ($numberLinesText / 3 * 2)) {	# Less than 2/3 different = more than 1/3 identical
						if ($numberLinesScoreOnly < $numberLinesText / 2) {	# Less than 1/2 different = more than 1/2 identical
						
							my $coreLineScore = $score{$key}{'coreLineCur'};
							my $coreLineScoreText = $scoreOriginalText[$coreLineScore - 1];	# Array element count starts at 0, while our line
							my $coreLineCurText = $originalText[$coreLineCur - 1];			# count starts at 1.

#error( $q, "workKey is $workKey<br>\nkey is $key<br>\nnumberLinesScoreOnly is $numberLinesScoreOnly<br>\nnumberLinesOriginalText is $numberLinesOriginalText<br>\ngapHitLineCoreLineCur is $gapHitLineCoreLineCur<br>\ncoreLineScore is $coreLineScore<br>\ncoreLineCur is $coreLineCur<br>\ncoreLineScoreText is $coreLineScoreText<br>\ncoreLineCurText is $coreLineCurText" ) if $key =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;
							if ($coreLineScoreText eq $coreLineCurText) {

								my $gapHitLineCoreLineScore;
								my $hitLineScore = $score{$key}{'hitLine'};
								if ($coreLineScore < $hitLineScore) {
									$gapHitLineCoreLineScore = $hitLineScore - $coreLineScore;
								} else {
									$gapHitLineCoreLineScore = $coreLineScore - $hitLineScore;
								}
#error( $q, "workKey is $workKey<br>\nkey is $key<br>\nnumberLinesScoreOnly is $numberLinesScoreOnly<br>\nnumberLinesOriginalText is $numberLinesOriginalText<br>\ncoreLineScore is $coreLineScore<br>\ncoreLineCur is $coreLineCur<br>\ncoreLineScoreText is $coreLineScoreText<br>\ncoreLineCurText is $coreLineCurText<br>\ngapHitLineCoreLineCur is $gapHitLineCoreLineCur<br>\ngapHitLineCoreLineScore is $gapHitLineCoreLineScore" ) if $key =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;
								if ($gapHitLineCoreLineCur < $gapHitLineCoreLineScore) {
									delete $score{$key};				# Camel3 29.2.24, Cookbook 5.3.
									delete $scoreWork{$key};			# The smaller the gap between hitLine and coreLine, the greater the 
									delete $scoreTotal{$key};			# chance that the reference in the work title really fits what we
									--$newRecsCounter;					# have established as the quotation core (in the CLCLT we can be sure, 
#error( $q, "i got here, key is $key" ) if $key =~ /BedaUenerabilisInLucaeeuangeliumexpositioCl1356000100010682/;
									last;								# in the TLG it depends on whether or not the same number of lines be-
								} else {								# fore and after hitLine have been exported.)
									@newText = ();						# Empties the @newText array; Learning 3.2, Camel 2.3.4.
									@matchLines = ();					# Empties the @matchLines array; Learning 3.2, Camel 2.3.4.
									$fileLineCounter = 0;
									$matchedWords = "";					# For debugging
									next LINE;
								}
							}	
						}
					}
				}
				
				## The following block of code keeps the score hash to a maximum of 100 entries. Only the 100 quotations and allusions that
				## get the greatest number of points are retained. This is done to save memory, as the whole score hash gets loaded into
				## RAM, which can lead to performance and stability problems (search file gets corrupted when CGI crashes while the score 
				## hash is being written to.) Also, thousands of search results would occupy gigabites of harddisk space.

				$scoreSize = scalar(keys(%scoreWork));					# Initializes a variable by the name of scoreSize and stores the num-
																		# ber of keys of the scoreWork hash in it; Camel3 2.9. The scoreWork 
																		# hash contains the same keys as the score hash, but not much else, 
																		# so we won't run into memory and performance problems with the keys 
																		# function below.
				if ($scoreSize > 99) {									# If the value stored in the scoreSize variable is greater than 99, 
																		# the following block of code is executed. 
					@records = sort { $scoreTotal{$b} <=> $scoreTotal{$a} } keys %scoreTotal;	# Sorts the keys of the scoreTotal2 hash by their associ-
																		# ated values; Cookbook 5.9. 
					my $keyOneHundred = $records[99];					# Cookbook 4.0. As count begins at 0, element 99 is the one 
																		# hundredth element.
					my $pointsOneHundred = $scoreTotal{$keyOneHundred};	# We look up how many points the one hundredth element got (this is 
																		# the element with the lowest number of points).
					if ($pointsTotal < $pointsOneHundred) {				# Camel3 1.6.2.4. If the current text scored fewer points than the
																		# one hundredth element in the score hash, we move to the next.
						@newText = ();									# Empties the @newText array; Learning 3.2, Camel 2.3.4.
						@matchLines = ();								# Empties the @matchLines array; Learning 3.2, Camel 2.3.4.
						$fileLineCounter = 0;
						$matchedWords = "";								# For debugging
						next LINE;										# Skips to the end of the current while (<FH>) loop iteration and 
						
					}

					my $deleteSize = $scoreSize - 99;	# deleteSize will be 1 except when QuotationFinder is reading legacy
														# hashes that were allowed to have more than 100 records.
					
					my @deleteKeys = splice(@records, -$deleteSize);	# Removes the number of elements stored in the deleteSize variable 
																		# from the records array and stores them in the deleteKeys array; 
																		# Cookbook 4.11, Camel3 29.2.160. The 99 records with the highest 
																		# score will be preserved, the rest (usually 1 record) will be 
																		# deleted to make space for the new record.
					foreach my $deleteKey (@deleteKeys) {
					
						delete $score{$deleteKey};						# Camel3 29.2.24, Cookbook 5.3.
						delete $scoreWork{$deleteKey};
						delete $scoreTotal{$deleteKey};
					
					}
				}
			
				$score{$workKey} = {									# Assigns values to the multidimensional hash called score, using the
					'Work'			=>	$work,							# workKey variable as the top level key, the left hand column as mid-
					'Passage'		=>	$passage,						# level keys, and the right hand column as values; Cookbook 5.1, Camel 
					'Text'			=>	[ @newText ],					# 4.7.5.1.
					'Occurrence'	=>	$sumPointsOcc,
					'Position'		=>	$sumPointsPos,
					'Density'		=>	$pointsDens,
					'hitLine'		=>	$hitLine,
					'coreLineCur'	=>	$coreLineCur,
					'matchedWords'	=>	$matchedWords,
					'matchLines'	=>	[ @matchLines ],
					'originalText'	=>	[ @originalText ],
#						'Points'		=>	{ %points },
				};														# Closes $score{$workKey} block; Nutshell 4.3.

				$scoreWork{$workKey} = $work;							# Assigns a value to the scoreWork hash, using the workKey variable as
																		# the key and the work variable as the value; Cookbook 5.1.
				$scoreTotal{$workKey} = $pointsTotal;					# Assigns a value to the scoreTotal hash, using the workKey variable as
																		# the key and the pointsTotal variable as the value; Cookbook 5.1.
				++$newRecsCounter;
				
				untie %score;											# Closes $mldbScoreFile, $dbScoreWorkFile, and $dbScoreTotalFile; Cookbook 
				untie %scoreWork;										# 14.1, CGI 10.2 (241).
				untie %scoreTotal;										# 14.1, CGI 10.2 (241).

#				print "<p>The score for $work has been added to the database.</p>";	# For debugging.
				
				@newText = ();										# Empties the @newText array; Learning 3.2, Camel 2.3.4.
				@matchLines = ();									# Empties the @matchLines array; Learning 3.2, Camel 2.3.4.
				$fileLineCounter = 0;
				$matchedWords = "";									# For debugging
			
			}															# Closes the if ($textEnd ne "yes") ... else  block; Nutshell 4.3.
			@matchLines = ();											# Empties the @matchLines array; Learning 3.2, Camel 2.3.4.
		}																# Closes the while (<$file>) loop; Nutshell 4.3.
		close($file);													# Closes the file associated with FH; Learning 10.2, Camel 8.3.4.

#my @recordsScore = sort (keys %score);
#my $countScore = @recordsScore;
#print "<br>countScore is $countScore";

#my @recordsScoreWork = sort (keys %scoreWork);
#my $countScoreWork = @recordsScoreWork;
#print "<br>countScoreWork is $countScoreWork";

#my @recordsScoreTotal = sort (keys %scoreTotal);
#my $countScoreTotal = @recordsScoreTotal;
#print "<br>countScoreTotal is $countScoreTotal";

	}																	# Closes the foreach $fileName loop; Nutshell 4.3.

	untie %seenWorks;		 											# 14.1, CGI 10.2 (241).

#	print Dumper(%score);
	
	my $newRecsMessage;
	my $x = "new" if $oldScoreWorkFile;									# If there had been a dbScoreWorkFile before this search, we add the 
																		# word "new" to the number of matches indicated to the user.
	if ($newRecsCounter > 99) {
		$newRecsMessage = "<br>\n      Many $x matches for your Search Text found, the top 100 retained.";
	} elsif ($newRecsCounter > 1) {
		$newRecsMessage = "<br>\n      $newRecsCounter $x matches for your Search Text found.";
	} elsif ($newRecsCounter == 1) {
		$newRecsMessage = "<br>\n      1 $x match for your Search Text found.";
	} elsif ($newRecsCounter == 0) {
		$newRecsMessage = "<br>\n      No new matches for your Search Text found.";
	}

#error( $q, "scoreSize is '$scoreSize'" );
#	if ($scoreSize < 1) {												# Bad move. $scoreSize will be empty if the current upload only con-
																		# tains texts already searched.
	if (-e $dbScoreWorkFile) {
	
		print <<HTML;
<table width="750" border="0">
  <tr>
    <td width="150">&nbsp;</td>
    <td width="588">&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      Search completed. $newRecsMessage
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      <input type="submit" name="viewScore" value="View Results">
    </td>
  </tr>
</table>
HTML
	
	} else {
	
		print <<HTML;
<table width="750" border="0">
  <tr>
    <td width="150">&nbsp;</td>
    <td width="588">&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      Search completed. No matches for your search text found.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      <input type="submit" name="viewNavigation" value="View Navigation Page">
    </td>
  </tr>
</table>
HTML

	}
	
	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "mt",
				-default  => $mt,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).

}																		# Closes the create_score subroutine; Camel3 6.2, Cookbook 10.0.


sub print_score{														# Begins the print_score subroutine. This subroutine displays the score
																		# to the user. 
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my (%score2, %scoreWork2, %scoreTotal2);											# Declares private variables that exist only within the innermost en-
	my @records;														# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	my $workKey;

	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Results',											# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form;

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );													# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
  
	error( $q, "userDir is an empty string, I'm in sub print_score." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub print_score." ) if ($searchDir eq "");
	my $mldb = tie %score2, 'MLDBM', $mldbScoreFile, O_RDONLY, 0644 or error( $q, "Can't open tie 2 to MLDBM file: mldbScoreFile is $mldbScoreFile $!" );	# For debugging
	my $dbWork = tie %scoreWork2, 'DB_File', $dbScoreWorkFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File file: dbScoreWorkFile is dbScoreWorkFile $!" );
	my $dbTotal = tie %scoreTotal2, 'DB_File', $dbScoreTotalFile, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to DB_File file: dbScoreTotalFile is $dbScoreTotalFile $!" );
																		# Associates the database file whose path is stored in the mldbScore-
																		# File/dbScoreTotalFile variable with the score2/scoreTotal2 hash so that, 
																		# using the MLDBM/DB_File module, any changes to the hash are saved to 
																		# the file (which is created with write access for us but no one else 
																		# in case it doesn't exist yet); Cookbook 14.1, CGI 7.4 (191), DBI 2.7 
																		# (32), 2.9 (51), Cozens 435.
																		# Can fail without error message! Be extra careful about path name!

	undef $mldb;														# Frees up the memory associated with the objects; Camel3 29.2.187, 
	undef $dbWork;														# Cookbook 11.0.
	undef $dbTotal;

#my @keys2 = keys %score2;
#my $countScore2 = @keys2;
#print "<br>countScore2 is $countScore2";

#my @keysWork2 = keys %scoreWork2;
#my $countScoreWork2 = @keysWork2;
#print "<br>countScoreWork2 is $countScoreWork2";

#my @keysTotal2 = keys %scoreTotal2;
#my $countScoreTotal2 = @keysTotal2;
#print "<br>countScoreTotal2 is $countScoreTotal2";

	if ($sortOrder eq 'Total') {										# If the value stored in the sortOrder variable is 'Total,' the fol-
																		# lowing block of code is executed; Camel3 3.12. sortOrder is taken
																		# from a parameter passed on through cgi.pm from user input.
		@records = sort { $scoreTotal2{$b} <=> $scoreTotal2{$a} } keys %scoreTotal2;	# Sorts the keys of the scoreTotal2 hash by their associ-
																		# ated values; Cookbook 5.9. 
																		# THIS OPERATION OCCASIONALLY CRASHES THE DISPLAY SUBROUTINE. IT IS NOT
																		# CLEAR TO ME YET UNDER WHAT CIRCUMSTANCES THIS IS THE CASE. SEE CAMEL3
																		# 29.2.22, 29.2.79, COOKBOOK 5.4: THERE'S A PROBLEM USING THE keys 
																		# FUNCTION WITH LARGE HASHES.
	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.
		@records = sort (keys %scoreWork2);								# Sorts the keys of the scoreWork2 hash alphabetically; Cookbook 5.9. Be-
																		# cause the first part of the key is the author name, followed by the
																		# name of the work, this results in an ordering by author and work.
	}																	# Closes the else block; Nutshell 4.3.															#ACHTUNG: SPEICHERPROBLEM; CAMEL 3.2.79.
	
	# UM BENUTZERDEFINIERTE SORTIERORDNUNG ZU VERWIRKLICHEN: AUS BENUTZEREINGABEN DYNAMISCH PERL CODE ERZEUGEN UND MIT eval AUSWERTEN; CF. CA-
	# MEL 3.2.153

#	print "<p>\$sortOrder = $sortOrder</p>";							# For debugging.
#	foreach my $record (@records) {										# For debugging.
#		print "<p>$record</p>";
#	}
	
	# DIE FOLGENDE TECHNIK STAMMT AUS DEM FILE dbAnnotated.cgi AUS DEM DBMan ORDNER. INDEM IN DEN LINK EIN ACTION-ATTRIBUT EINGEBAUT WIRD, DAS AUF
	# DIE (ZUKÜNFTIGE) %score2-SUBROUTINE VERWEIST,
	# KANN DAS ERNEUTE DURCHSUCHEN DER GROSSEN FILES ÜBERSPRUNGEN WERDEN; VGL. CGI PROGRAMMING S. 275, PERL AND CGI S. 57. DAMIT DIES ABER FUNK-
	# TIONIERT, MUSS DIE DB_File FEHLERMELDUNG VERSCHWINDEN, DAMIT DAS SCRIPT NICHT AM ENDE DER %score-SUBROUTINE SCHON ABSCHMIERT...
	# DIE DB_File FEHLERMELDUNG ***IST*** VERSCHWUNDEN IN APACHE / MAC OS X!!!!!!!

	my ($nextPage, $prevPage, $left, $right, $lower, $upper, $pageLinks, $i, $first, $last, $lastPage);
																		# Declares private variables that exist only within the innermost en-
																		# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	my $numRecs = @records;
#print "\nnumRecs is $numRecs\n";
	my $maxRecs = 5;												# stores the value 5 in the maxRecs variable; Learning 2.6.
																		# This determines the maximum number of records displayed per page.

	# If we have more records than we want to display on one page, we build a pagelink toolbar for navigating the pages.
	if ($numRecs > $maxRecs) {											# If the value stored in the numRecs variable is greater than the one
																		# stored in the maxRecs variable, the following block of code is 
																		# executed; Learning 2.4.2, Camel 2.5.11. We only want to build the
																		# toolbar if we have more records than we can display on one page.
		$nextPage = $page + 1;											# Increases/diminishes the page variable by 1 and stores the results
		$prevPage = $page - 1;											# in the nextPage/prevPage variable; Learning 2.4.1. This will be used 
																		# for the [Next]/[Previous] links in the toolbar.
		$lastPage = $numRecs / $maxRecs;								# Divides the value stored in the numRecs variable by the one stored in
																		# the maxRecs variable; Learning 2.4.1.
		$lastPage = int $lastPage + 1 unless ($lastPage == int $lastPage);	# Takes the integer portion of the value stored in the lastPage
																		# variable, adds one, and replaces the value previously stored in the
																		# lastPage variable with the results unless the old lastPage value is 
																		# equal to the integer portion of the same; Camel 3.2.76. This   
																		# operation rounds up the results of the division above in case it isn't
																		# an integer.
																		# THE SAME EFFECT COULD BE HAD BY USING THE ceil() FUNCTION OF THE 
																		# POSIX MODULE, BUT I GUESS IT'S NOT WORTH THE OVERHEAD; Cookbook 2.3.

		# We now calculate how many pages we have to the left and the right of the current page.
		$left  = $page - 1;												# Subtracts 1 from the value stored in the page variable and stores the
																		# results in the variable called left; Learning 2.6. This is how many 
																		# pages we have to the left of the current page.
		$right = $lastPage - $page;										# Subtracts the value stored in the page variable from the one stored 
																		# in the lastPage variable, and stores the results in the variable 
																		# called right; Learning 2.4.1. This is how many pages we have to the
																		# right of the current page.

		# In case we have so many pages that we can't list links to every one of them in the toolbar, we need a lower and upper limit for the
		# page links we are going display to the left and the right of the current page, with special provisions for when we are near the first
		# or the last page.
		if ($right < 7) {												# If the value stored in the variable called right is less than 7, the
																		# following block of code is executed; Learning 2.4.2, Camel 2.5.11. 
			$lower = $lastPage - 14;									# Subtracts 14 from the value stored in the lastPage variable and puts 
																		# the results in the lower variable; Learning 2.4.1. If we are on one of
																		# the last 7 pages, we will display the whole right end of the page  
																		# link spectrum.
		} else {														# If the condition above is not met, the following block of code is
																		# executed; Learning 4.2.
			$lower = $page - 7;											# Takes the value stored in the page variable, subtracts 7 from it, and
																		# stores the results in the lower variable; Learning 2.4.1. This will be
																		# the lower limit for page number links in the toolbar if we have more 
																		# than 7 pages on the left.
																		# We don't need to worry about values for $lower that are less than 1,
																		# as they will automatically be ignored by the for loop below.
		}																# Closes the if ... else block; Learning 4.1.
		if ($left < 7) {												# If the value stored in the variable called right is less than 7, the
																		# following block of code is executed; Learning 2.4.2, Camel 2.5.11. 
			$upper = 15;												# Assigns the value of 15 to the variable called upper; Learning 2.6. 
																		# If we are on one of the first 7 pages, we will display the whole left 
																		# end of the page link spectrum.
		} else {														# If the condition above is not met, the following block of code is
																		# executed; Learning 4.2.
			$upper = $page + 7											# Takes the value stored in the page variable, adds 7 to it, and stores
																		# the results in the upper variable; Learning 2.4.1. This will be the
																		# upper limit for page number links in the toolbar if we have more than
																		# 7 pages on the right.
																		# We don't need to worry about values for $upper that are greater than
																		# $lastPage, as they will automatically be ignored by the for loop
																		# below.
		}																# Closes the if ... else block; Learning 4.1.

		# Now we build the HTML toolbar by appending piece by piece to the pageLinks variable.
		($lower > 1)	and ($pageLinks .= qq~<a href="$qfUrl?action=viewScore&page=1&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[First]</a> ~);
																		# Checks to see if the parenthesis to the left of "and" is true, i.e.
																		# if the value stored in the variable called lower is greater than 1, 
																		# and, if so, executes the parenthesis to the right of "and," i.e. 
																		# appends the HTML link to page 1 to the string stored in the pageLinks 
																		# variable; Learning 2.6.1, Camel 2.5.14, 2.5.20, 8.4, Cookbook 1.0, 
																		# 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl and CGI 56.
		($page > 1)		and ($pageLinks .= qq~<a href="$qfUrl?action=viewScore&page=$prevPage&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[Previous]</a> ~);
																		# Checks to see if the parenthesis to the left of "and" is true, i.e.
																		# if the value stored in the variable called page is greater than 1, 
																		# and, if so, executes the parenthesis to the right of "and," i.e. 
																		# appends the HTML link to the previous page to the string stored in  
																		# the pageLinks variable; Learning 2.6.1, Camel 2.5.14, 2.5.20, 8.4, 
																		# Cookbook 1.0, 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl 
																		# and CGI 56.
		for ($i = 1; $i <= $lastPage; $i++) {							# Sets the initial value of the counter variable i to 1, determines 
																		# that this will go on as long as the counter is less than or equal to 
																		# the value stored in the lastPage variable, sets the auto-increment
																		# operator in motion, and executes the following block for every value
																		# of i that meets the condition; Learning 4.4.
			if ($i < $lower) {											# If the value of the i counter is less than that of the variable 
																		# called lower, the following block of code is executed; Learning 
																		# 2.4.2.
				$pageLinks .= " ... " if ($lower > 2);					# Appends ellipsis points to the pageLinks variable if the value stored
																		# in the lower variable is greater than 2; Learning 2.4.2.
				$i = ($lower - 1);										# Subtracts 1 from the value stored in the lower variable and puts the
																		# results in the i counter; Learning 2.4.1. We can skip all values of i
																		# until we are just below $lower, because we won't display them in the 
																		# pagelinks toolbar.
				next;													# Causes execution to skip past the rest of the for block without
																		# terminating the block; Learning 9.2.
			} elsif ($i > $upper) {										# If the value of the i counter is greater than that of the variable 
																		# called upper, the following block of code is executed; Learning 
																		# 2.4.2.
				$pageLinks .= " ... " if ($lastPage - $upper > 1);		# Appends ellipsis points to the pageLinks variable if the difference  
																		# between the values stored in the lastPage and upper variables is 
																		# greater than 1; Learning 2.4.2.
				last;													# Causes execution to break out of the for block and to continue with
																		# the statement immediately following the block; Learning 9.1.
			} elsif ($i == $page) {										# If the value of the counter i is equal to the value stored in the
																		# page variable, the following block of code is executed; Learning 
																		# 2.4.2.
				$pageLinks .= qq~$i ~;									# Appends the current value of the i counter to the pageLinks variable;
																		# Cookbook 1.0, 4.1. We don't need to provide a link to the current 
																		# page, since we are on it.
			} else {													# If none of the conditions above are met, the following block of code
																		# is executed; Learning 4.2.
				$pageLinks .= qq~<a href="$qfUrl?action=viewScore&page=$i&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">$i</a> ~;
																		# Appends the HTML link to the page indicated by the current value of i
																		# to the string stored in the pageLinks variable unless the current
																		# value of the page variable is equal to the one of the lastPage
																		# variable; Learning 2.6.1, Cookbook 1.0, 4.1, HTML Definitive 7.3.3
																		# (219f), CGI 101 111f, Perl and CGI 56.
			}															# Closes the if ... elsif ... else block; Learning 4.1.
		}																# Closes the for loop; Learning 4.1.
		$pageLinks .= qq~<a href="$qfUrl?action=viewScore&page=$nextPage&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[Next]</a> ~ unless ($page == $lastPage);
																		# Appends the HTML link to the next page to the string stored in the 
																		# pageLinks variable unless the current value of the page variable is
																		# equal to the one of the lastPage variable; Learning 2.6.1, Cookbook 
																		# 1.0, 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl and CGI 
																		# 56. We don't want to provide a link to the next page if we are on the
																		# last one.
		$pageLinks .= qq~<a href="$qfUrl?action=viewScore&page=$lastPage&so=$sortOrder&id=$id&mo=$mo&se=$se&en=$en&mt=$mt">[Last]</a> ~ if ($lastPage > $upper);
																		# Appends the HTML link to the last page to the string stored in the 
																		# pageLinks variable if the value stored in the lastPage variable is
																		# greater than the one in the upper variable; Learning 2.6.1, Cookbook 
																		# 1.0, 4.1, HTML Definitive 7.3.3 (219f), CGI 101 111f, Perl and CGI 
																		# 56. We only provide a [Last] link if there is no link to the last 
																		# page by page number.
		
# Slice the @records to only return the ones we want, only have to do this if the results are sorted.					#ONLY THE HITS WE WANT
#		if (exists $in{'sb'}) {			
			$first = $maxRecs * ($page - 1);
			$last  = $first + $maxRecs - 1;		
			if ($last > $#records) {
				$last = $#records;
			}
			@records = @records[$first .. $last];
#		}
	}
	
#From Webreview.com (Brent Michalski) again:
# Bold the results 
#	if ($db_bold and $in{'view_records'}) {
#		for $i (0 .. (($#records+1) / ($#db_cols+1)) - 1) {
#			$offset = $i * ($#db_cols+1);
#			foreach $field (@search_fields) {				
#				$hits[$field + $offset] =~ s,(<[^>]+>)|($regexp_bold[$field]),defined($1) ? $1 : "<B>$2</B>",ge;
#			}
#		}
#	}
#	return ("ok", @records);																							#RETURN VALUE IS TRANS-
																														#PORTED VIA view_records
																														#TO html_view_success
																														#IN html.pl;
																														#CF. PERL AND CGI 123
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <h5>QuotationFinder Results</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Results" target="Help">Help&nbsp;</a></td>
HTML

	if ($numRecs == 1) {
		print "<td class=roman>QuotationFinder has found 1 match for your Search Text.</td>";
 	} elsif ($numRecs == 100) {
 		print "<td class=roman>QuotationFinder has found many matches for your Search Text.<br>The top 100 have been retained.</td>";
 	} else {
 		print "<td class=roman>QuotationFinder has found $numRecs matches for your Search Text.</td>";
 	}

	print <<HTML;
     </tr>
    <tr> 
      <td>&nbsp;</td>
      <td>&nbsp;</td>
    </tr>
HTML

	if ($pageLinks ne "") {
	
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>$pageLinks</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}

	foreach $workKey (@records) {					# Camel 4.7.5.3. Funktioniert! Vgl. aber bei Effizienzproblemen
  													# die Warnung in der MLDBM-Dokumentation (am Ende von mldbm.pm
  																		# oder - schöner - im file "search.cpan.org on MLDBM").
  																			# For debugging.

		my $class;
		if ($en eq "Roman") {
			$class = "roman";
		} else {
			$class = "greek";
		}
	  
		print <<HTML;
  <tr> 
    <td class=roman align="right">Author and Work:</td>
    <td><b>$score2{$workKey}{'Work'}</b></td>
  </tr>
HTML

		if ($en eq "Roman") {
			print <<HTML;
  <tr> 
    <td class=roman align="right">Passage:</td>
    <td class=roman><b>$score2{$workKey}{'Passage'}</b></td>
  </tr>
HTML
		}																	# Closes the if ($en eq "Roman") block; Nutshell 4.3.

		print <<HTML;
  <tr> 
    <td class=roman align="right">Text:</td>
    <td class=$class>
@{ $score2{$workKey}{'Text'} }
    </td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
#  <tr> 
#    <td class=roman align="right">Points Occurrence:</td>
#    <td class=roman>$score2{$workKey}{'Occurrence'}</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">Points Position:</td>
#    <td class=roman>$score2{$workKey}{'Position'}</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">Points Density:</td>
#    <td class=roman>$score2{$workKey}{'Density'}</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">Points Total:</td>
#    <td class=roman>$scoreTotal2{$workKey}</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">workKey:</td>
#    <td class=roman>$workKey</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">hitLine:</td>
#    <td class=roman>$score2{$workKey}{'hitLine'}</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">coreLineCur:</td>
#    <td class=roman>$score2{$workKey}{'coreLineCur'}</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">matchedWords:</td>
#    <td class=roman>$score2{$workKey}{'matchedWords'}</td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">matchLines:</td>
#    <td class=$class>
#@{ $score2{$workKey}{'matchLines'} }
#    </td>
#  </tr>
#  <tr> 
#    <td class=roman align="right">originalText:</td>
#    <td class=$class>
#@{ $score2{$workKey}{'originalText'} }
#    </td>
#  </tr>
#  <tr>
#    <td>&nbsp;</td>
#    <td>&nbsp;</td>
#  </tr>
#HTML

	}															# Ends foreach $workKey block.

	if ($pageLinks ne "") {
	
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>$pageLinks</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}

	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td> 
      <input type="submit" name="viewNavigation" value="View Navigation Page">
    </td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
HTML

	if ($numRecs > 1) {
		if ($sortOrder eq 'Total') {
			print "      Results sorted on Points Total. For sorting on Author and Work click ",
				"<a href='$qfUrl?action=viewScore&page=1&so=Work&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>here</a>.\n";	#Perl and CGI 56.
		} else {
			print "      Results sorted on Author and Work. For sorting on Points Total click ",
				"<a href='$qfUrl?action=viewScore&page=1&so=Total&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>here</a>.\n";	#Perl and CGI 56.
		}
	}
	print "      <p>For a list of the files searched so far click ",
		"<a href='$qfUrl?action=viewFilesSearched&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>here</a>.\n";	#Perl and CGI 56.
		
	print <<HTML;
    </td>
  </tr>
</table>
HTML

	untie %score2;														# Closes $mldbScoreFile; Cookbook 14.1, CGI 10.2 (241).
	untie %scoreWork2;													# Closes $dbScoreWorkFile; Cookbook 14.1, CGI 10.2 (241).
	untie %scoreTotal2;													# Closes $dbScoreTotalFile; Cookbook 14.1, CGI 10.2 (241).

#	printf ("Free Memory: %0.2f MB\n", mbytes(FreeMem()));			# For debugging; MacPerl 193.
#	printf ("Max Memory: %0.2f MB\n", mbytes((MaxMem())[0]));
	
	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "mt",
				-default  => $mt,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).

}																		# Closes the print_score subroutine; Camel3 6.2, Cookbook 10.0.


sub print_upload_form {													# Begins the print_upload_form subroutine; Camel3 6.2, Cookbook 10.0.  
																		# This subroutine prints the form for choosing the files that are to 
																		# be searched for quotations. Cf. CGI 5.2 (97), CGI.pm 3.9 (152).
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my $uploadNumber = $q->param('un') || '1';								# Fills the uploadNumber variable with the value of the parameter 
																		# called un, or with 1 if no such parameter exists; CGI 5.2 (96f), 11.2
																		# (273-280).
	my $corpus;
	
	# The following JavaScript does form validation; Flanagan 10.3.1 (159), 15.4 (264); CGI.pm 3.12 (176); CGI 7.2 (168)

	my $javaScript=<<END;

		function validateFile()
		{
			var file = this.document.chooseFile.file.value;				// Doesn't work as browsers prepend path information to the filename,
//			var pattern = /^\\W/;										// including slashes, quotation marks, etc.
			if (file == "") {
				alert("Please choose a file.");
				return false;
			}
//			if (pattern.test(file) == 1) {
//				alert("File names must start with a letter (a-z/A-Z), a number, or an underscore (_). file is " + file);
//				return false;
//			}
			alert("QuotationFinder is about to start receiving your data. Depending on the size of your file(s) and the speed of your Internet connection, it may take a while until you can see any sign that progress is being made. Please be patient. Click OK to continue.");
		}
END

	print $q->start_html(												# Uses the start_html and start_multipart_form functions from CGI.pm to
			-title=>'Choose File',										# print the starting HTML and FORM tags; CGI.pm 255, 259, CGI 5.3 (110).
			-script=>$javaScript,
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_multipart_form(
			-name=>'chooseFile',
			-onSubmit=>"return validateFile(this)",
		);


	$q->cgi_error and error( $q, "Error transferring file: " . $q->cgi_error );	# Checks for errors and calls the error subroutine, passing it
																		# an error message, if one has occurred; CGI 5.2 (99).

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );												# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.
  
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td> 
HTML

	if ($uploadNumber == 1) {											# If the value stored in the uploadNumber variable equals 1, the fol-
																		# lowing block of code is executed; Camel3 3.12.
		print "<h5>Choose File</h5>";									# Prints some HTML; CGI 5.4 (111).
	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		print "<h5>Choose Files</h5>";									# Prints some HTML; CGI 5.4 (111).
	}																	# Closes the if... else... block; Nutshell 4.3.
        
	if ($en eq "Roman") {												# If the value stored in the en variable is "Roman", the fol-
																		# lowing block of code is executed; Camel3 3.12.
		$corpus = "CLCLT";												# Stores the string "CLCLT" in the variable named corpus.

	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		$corpus = "TLG";												# Stores the string "TLG" in the variable named corpus.

	}																	# Closes the if... else... block; Nutshell 4.3.
        
	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Choose_File" target="Help">Help&nbsp;</a></td>
    <td class=roman>
      Using your $corpus software, search for a word from your Search<br>
      Text and save the resulting passages with their context to a<br>
HTML
	
	if ($en ne "Roman") {												# If the value stored in the en variable is not "Roman", the fol-
																		# lowing block of code is executed; Camel3 3.12.
		print <<HTML;
      file (Pandora: Beta code, TLG Workplace: RTF).<br>
HTML
	
	} else {
	
		print <<HTML;
      file.<br>
HTML
	
	}
	
	print <<HTML;
      Repeat this for every important word in your Search Text.
HTML

	if ($uploadNumber == 1) {											# If the value stored in the uploadNumber variable equals 1, the fol-
																		# lowing block of code is executed; Camel3 3.12.
		print "<p>Then return to QuotationFinder and choose one of these files to have<br>it searched for quotations. Add a file description if you like.";
																		# Prints some HTML; CGI 5.4 (111).
	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		print "<p>Then return to QuotationFinder and choose the files to be searched<br>for quotations. Add file descriptions if you like.";
																		# Prints some HTML; CGI 5.4 (111).
	}																	# Closes the if... else... block; Nutshell 4.3.
        
	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	for my $i (1 .. $uploadNumber) {									# For the whole range from 1 to the value stored in the uploadNumber
																		# variable, the following block of code is executed; Camel3 6.8, Nut-
																		# shell 4.5.11.1. This determines how many file upload and description
																		# fields are displayed.
		print <<HTML;
  <tr> 
    <td class=roman align="right">
      File:
    </td>
    <td class=roman> 
      <input type="file" name="file" maxlength="9999" size="48">
    </td>
  </tr>
  <tr> 
    <td class=roman align="right">
      Description:
    </td>
    <td class=roman> 
      <input type="text" name="description" maxlength="9999" size="48">
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	}																	# Closes the for loop; Nutshell 4.3.
	
	if ($uploadNumber == '1') {											# If the value stored in the uploadNumber variable equals 1, the fol-
																		# lowing block of code is executed; Camel3 3.12.
																	# Perl and CGI 3.12 (56).
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      To have QuotationFinder search multiple files at once, click <br>
        on one of the following links: up to 
        <a href='$qfUrl?action=newScore&un=5&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>5</a>, 
        <a href='$qfUrl?action=newScore&un=10&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>10</a>, 
        <a href='$qfUrl?action=newScore&un=20&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>20</a>, 
        <a href='$qfUrl?action=newScore&un=50&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>50</a>, or 
        <a href='$qfUrl?action=newScore&un=100&id=$id&mo=$mo&se=$se&en=$en&mt=$mt'>100</a> files.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}																	# Closes the if block; Nutshell 4.3.
	
	unless ($en eq "Roman") {
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Mark whether the file was exported from
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='fo' value='Pandora' checked></td>
    <td class=roman>
      Pandora or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='fo' value='TLG_Workplace'></td>
    <td class=roman>
      TLG Workplace.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}
	
	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Choose whether the results are to be sorted based on
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='so' value='Total' checked></td>
    <td class=roman>
      similarity to Search Text or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='so' value='Work'></td>
    <td class=roman>
      author and work in alphabetical order.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML

	if (-e "$dbScoreTotalFile") {											# If the file whose name is stored in the dbScoreTotalFile variable exists, 
																		# the following block of code is executed; Camel 1.5.7, Cozens 6.5 
																		# (208). We only want to provide users with a link to view the score if
																		# the score exists.
		print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Choose whether previous results are to be
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='pr' value='keep' checked></td>
    <td class=roman>
      kept or
    </td>
  </tr>
  <tr> 
    <td class=roman align="right"><input type='radio' name='pr' value='delete'></td>
    <td class=roman>
      deleted.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
HTML
	}																	# Closes the if (-e "$dbScoreTotalFile") block; Nutshell 4.3.

	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td class=roman>
      Please be patient&#151;the search may take several minutes.
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      <input type="submit" name="chooseFileSubmit" value="Start Search">
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
</table>
HTML

	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "mt",
				-default  => $mt,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).
}																		# Closes the print_upload_form subroutine; Camel3 6.2, Cookbook 10.0.



#$CGI::POST_MAX = 1024 * 1500;   # Limit to 1500kb posts...


# The following textFiles subroutines for handling uploads are inspired by Meltzer/Michalski 7.4 (173-180).

sub get_names{															# Begins the get_names subroutine; Camel3 6.2, Cookbook 10.0. This sub-
																		# routine gets names and information on text files about to be up-
																		# loaded.
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my $prevResults = $q->param('pr') || 'keep';						# Uses CGI.pm's param function to access the pr parameter returned  
																		# by the browser when the user submits the upload fill-out form, pro-
																		# vides a default value if necessary, and stores the parameters in a  
																		# private variable; CGI.pm 5.3 (233), CGI 5.2 (96).
	my $counter = 0;													# Declares private variables that exist only within innermost enclosing
	my $counterBlank = 0;												# block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	my ($fullName, $fileName, %textFiles);
	
	if ($prevResults eq "delete") {

		unlink $mldbScoreFile;											# Removes the score files in case they exist; Learning 13.1, DBI 2.9 
		unlink $dbScoreWorkFile;										# (51).
		unlink $dbScoreTotalFile;
		unlink $mldbTextFiles;
		unlink $dbSeenWorksFile;
	}

	error( $q, "userDir is an empty string, I'm in sub get_names." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub get_names." ) if ($searchDir eq "");
	my $mldb = tie %textFiles, 'MLDBM', $mldbTextFiles, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM mldbTextFiles: $!" );
																		# Associates the database file whose path is stored in the mldbText-
																		# Files variable with the textFiles hash so that, using the MLDBM mo-
																		# dule, any changes to the hash are saved to the file (which is created
																		# with write access for us but no one else in case it doesn't exist 
																		# yet); Cookbook 14.1, CGI 7.4 (191), 10.2 (241), DBI 2.7 (32), 2.9 
																		# (51), Cozens 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	@fileNames = $q->param('file');										# Puts the values of all form fields named file in the array called 
																		# fileNames; Meltzer/Michalski 7.4 (165). There are multiple form 
																		# fields named file if the user chose to search several files at once 
																		# on the Choose File page.
	if (@fileNames < 2) {												# If the number of elements in the array called fileNames is less than 
																		# 2, the following block of code is executed; Camel3 29.2.84, Nutshell 
																		# 4.5.4.1.
		@fileNames = $q->upload('file');								# Takes CGI.pm's upload information and stores it in the fileNames ar-
																		# ray; CGI 5.2 (98). CGI.pm's upload method is now preferred over the
																		# param method, but it doesn't seem to work with more than one file, so
																		# we only use it accordingly.
	}																	# Closes the if block; Nutshell 4.3.
	@descriptions = $q->param('description');							# Puts the values of all form fields named description in the array 
																		# called descriptions; Meltzer/Michalski 7.4 (165). There are multiple 
																		# form fields named description if the user chose to search several 
																		# files at once on the Choose File page.

	foreach $fullName (@fileNames) {									# For each element of the fileNames array, the following block of code
																		# is executed with the element stored in the fullName variable; Camel3 
																		# 1.6.2.3.
		if ($fullName ne "") {											# If the value stored in the fullName variable is not an empty string,
																		# the following block of code is executed; Nutshell 4.5.4.2.
			$fileName = get_file_name($fullName);						# Calls the get_file_name subroutine, passes it the fullName variable,
																		# and stores the subroutine's results in the fileName variable; Camel3
																		# 6.2.
			$fileName =~ s/(\d*)(\.\w+)?$/($1||0) + 1 . $2/e while (exists $textFiles{$fileName});
																		# Takes the value stored in the fullName variable, matches any number 
																		# of digits, possibly followed by a dot and one or more word characters, up to the
																		# end of the string, and substitutes all of that with the results of the
																		# matched number (or 0 if there is none) plus 1 and the text matched by
																		# the second set of parentheses (which gets evaluated) as long as the 
																		# textfiles hash contains a key by the name of that value; CGI 5.2 
																		# (100), Friedl 1.4.11 (21), Cookbook 5.2, 6.0. The purpose of this is
																		# that in case a file by the same name was previously searched, the new
																		# file's name gets a number attached (or incremented, if there already
																		# was one) before the suffix so that the old file's description does
																		# not get overwritten.
			$textFiles{$fileName} = $descriptions[$counter];			# Creates a new entry in the textFiles hash, using the fileName vari-
																		# able as the key and the nth element of the descriptions array as the
																		# value, with n being the counter variable's value; Cookbook 5.1. If 
																		# the user chose to upload multiple files for searching, we use the 
																		# counter to safely match descriptions with fileNames.
		} else {														# If the above condition was not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
			$counterBlank++;											# Increments the counterBlank variable by one; Camel3 1.5.4. We need 
																		# this information for an error check below.
		}																# Closes the if... else... block; Nutshell 4.3.
		$counter++;														# Increments the counter variable by 1; Camel3 3.3. We need this infor-
																		# mation to match descriptions with file names.
	}																	# Closes the foreach block; Nutshell 4.3.

	untie %textFiles;													# Closes $mldbTextFiles; Cookbook 14.1, CGI 10.2 (241).

	if ($counterBlank == $counter) {									# If the value stored in the counterBlank variable is equal to the one 
																		# stored in the counter variable, the following block of code is exe-
																		# cuted; Camel3 3.12. If all elements of the fileNames array are blank, 
																		# no names of files to be uploaded have been transmitted.
		$message = "QuotationFinder has received no file.";				# Stores a message in the variable named message;
																		# Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if ($counterBlank == $counter) block; Nutshell 4.3. 
}																		# Closes the get_names subroutine; Camel3 6.2, Cookbook 10.0.


sub get_file_name{														# Begins the get_file_name subroutine; Camel3 6.2, Cookbook 10.0. This 
																		# subroutine makes sure the file to be uploaded really is a text file,
																		# and turns its name into something we want to use.
	my $fullName	= shift;											# Removes the first element of the @_ array (containing the values 
																		# passed to the subroutine) and stores it in the private fullName vari-
																		# able; Camel3 29.2.149.
error( $q, "fullName is blank: '$fullName'" ) if ($fullName eq "");
	my $fileinfo	= $q->uploadInfo($fullName);						# Gets information about the file to be uploaded and stores it in the
																		# fileinfo hash reference; CGI.pm 234.
	my $type		= $fileinfo->{'Content-Type'} || '';					# Gets the value 'Content-Type' using the fileinfo hash reference and 
																		# stores it in the type variable; CGI.pm 234.
#	my $info;
#	foreach (keys %{$fileinfo}) {
#		print "    <dt>$_</dt> <dd>$$fileinfo{$_}</dd>";
#		$info = $info . $$fileinfo{$_}
#	}
#	error( $q, "info is $info" );
#	if ( $type !~ m|^text/| and $type ne "") { 							# If the value stored in the type variable does not contain the pat-
#																		# tern between the | characters and is not an empty string, the follow-
#																		# ing block of code is executed; CGI.pm 3.9 (154), Meltzer/Michalski
#																		# 7.2 (150).
#		error( $q, "type is $type");
#		$message = "The file $fullName is not a text file.";			# Stores a message in the variable named message; Camel3 1.5.3.
#		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
#																		# parentheses; Camel3 6.2, 6.2.3.
#		exit															# Aborts the current subroutine; Camel3 29.2.35.
#	}																	# Closes the if block; Nutshell 4.3.

#	if ( $q->user_agent() =~ /win/i ) {									# If the value returned by CGI.pm's user_agent function contains a 
#																		# match for "win", the following block of code is executed; CGI.pm 5.3 
#																		# (229).
#		fileparse_set_fstype("MSDOS");									# Calls the fileparse_set_fstype() function from the File::Basename mo-
#																		# dule to set the file parse type to MSDOS; Meltzer/Michalski 7.2 
#																		# (156). This will cause the program to parse the directories and files
#																		# with the backslash.
#	} elsif ( $q->user_agent() =~ /mac/i ) {							# Else, if the value returned by CGI.pm's user_agent function contains a 
#																		# match for "mac", the following block of code is executed; CGI.pm 5.3 
#																		# (229).
#		fileparse_set_fstype("MacOS");									# Calls the fileparse_set_fstype() function from the File::Basename mo-
#																		# dule to set the file parse type to MacOS; Meltzer/Michalski 7.2 
#																		# (156).
#	}																	# Closes the if... elsif... block; Nutshell 4.3. If neither condition 
#	LÖST FEHLERMELDUNG AUS (TERMINAL)																		# was true, the file parsetype is not set--it stays with the default,
																		# Unix.
#	$fullName = basename($fullName);									# Calls the basename function from the File::Basename module and passes
#	LÖST FEHLERMELDUNG AUS (TERMINAL)									# it the fullName variable; Meltzer/Michalski 7.2 (174).
	$fullName =~ s/[^\w.-]/_/g;											# Gets the value of the fullName variable, substitutes anything that is
																		# not a word character (letters, digits, underscores), a period, or a 
																		# dash by an underscore, and puts the results back into the fullName
																		# variable; CGI 5.2 (100), Friedl 7.3.6 (241).
	if ( $fullName =~ /^(\w[\w.-]*)/ ) {								# If the value of the fullName variable starts with a word character 
																		# and continues with any number of word characters, periods, and dashes
																		# exclusively, the following block of code is executed; CGI 5.2 (100).
		$fullName = $1;													# Stores the text matched by the pattern between the parentheses in the
																		# fullName variable; Nutshell 4.4.5. This move untaints the fullName 
																		# variable; CGI 5.2 (102).
	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		$message = "File names must start with a letter (a-z/A-Z), a number, or an underscore (_).";	# Stores a message in the variable named message; Camel3 1.5.3.
		print_user_error($q, $id, $mo, $se, $en, $mt, $su, $message);						# Calls the print_user_error subroutine and passes it the values in the
																		# parentheses; Camel3 6.2, 6.2.3.
		exit;															# Aborts the current subroutine; Camel3 29.2.35.
	}																	# Closes the if... else... block; Nutshell 4.3.

	return($fullName);													# Returns from the subroutine and passes the fullName variable; Nut-
																		# shell 4.7.2
}																		# Closes the get_file_name subroutine; Camel3 6.2, Cookbook 10.0.


sub check_upload{															# Begins the check_upload subroutine; Camel3 6.2, Cookbook 10.0. This sub-
																		# routine gets names and information on text files about to be up-
																		# loaded.
	my ( $q, $id, $mo, $se, $en, $mt, $su, $fo, $file ) = @_;												# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my $foDisplay = $fo;
	$foDisplay =~ tr/_/ /;												# Camel3 5.2.4. We don't want to show ugly "TLG_Workplace" to users.
	
	my $warning1 = "<table width=\"750\" border=\"0\">\n"				# Stores a warning in the variable named warning1; Camel3 1.5.3.
				 . "  <tr>\n"
				 . "    <td width=\"150\">&nbsp;</td>\n"
				 . "    <td width=\"588\">&nbsp;</td>\n"
				 . "  </tr>\n"
				 . "  <tr>\n"
				 . "    <td>&nbsp;</td>\n"
				 . "    <td>\n"
				 . "      <h5>Error</h5>\n"
				 . "    </td>\n"
				 . "  </tr>\n"
				 . "  <tr>\n"
				 . "    <td>&nbsp;</td>\n"
				 . "    <td>\n";
	my $warning2 = "      <p>Try again by clicking <a href='$su'>here</a>.\n"
				 . "    </td>\n"
				 . "  </tr>\n"
				 . "</table>\n";

	if (/Excerpta CLCLT/) {
	
		if ($fo ne "CLCLT") {									# If the string contained in the id variable contains a nonword cha-
																# racter, the following block of code is executed; Nutshell 4.5.7, 
																# 4.6.4.
			print $warning1;
			print "      QuotationFinder was expecting a $foDisplay file, but '$file' appears to have been exported from the CLCLT.\n";
			print $warning2;
			print $q->end_html;											# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
			exit;												# Aborts the current subroutine; Camel3 29.2.35.
		}														# Closes the if ($id =~ /\W/) block; Nutshell 4.3. 
		
	} elsif (/Exported from Pandora/) {
	
		if ($fo ne "Pandora") {										# If the string contained in the id variable contains a nonword cha-
																# racter, the following block of code is executed; Nutshell 4.5.7, 
																# 4.6.4.
			print $warning1;
			print "      QuotationFinder was expecting a $foDisplay file, but '$file' appears to have been exported by Pandora.\n";
			print $warning2;
			print $q->end_html;											# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
			exit;												# Aborts the current subroutine; Camel3 29.2.35.
		}														# Closes the if ($id =~ /\W/) block; Nutshell 4.3. 
		
	} elsif (/SGkClassic/) {
	
		if ($fo ne "TLG_Workplace") {										# If the string contained in the id variable contains a nonword cha-
																# racter, the following block of code is executed; Nutshell 4.5.7, 
																# 4.6.4.
			print $warning1;
			print "      QuotationFinder was expecting a $foDisplay file, but '$file' appears to have been exported by TLG Workplace.\n";
			print $warning2;
			print $q->end_html;											# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
			exit;												# Aborts the current subroutine; Camel3 29.2.35.
		}														# Closes the if ($id =~ /\W/) block; Nutshell 4.3. 
		
	} elsif (/WL GreekTimes Ancient|Silver Humana|Graeca/) {

		if ($fo ne "TLG_Workplace") {										# If the string contained in the id variable contains a nonword cha-
																# racter, the following block of code is executed; Nutshell 4.5.7, 
																# 4.6.4.
			print $warning1;
			print "      QuotationFinder was expecting a $foDisplay file, but '$file' appears to have been exported by TLG Workplace.\n";
			print $warning2;
			print $q->end_html;											# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
			exit;												# Aborts the current subroutine; Camel3 29.2.35.
		}														# Closes the if ($id =~ /\W/) block; Nutshell 4.3. 
		
		print $warning1;
		print <<HTML;
      The file named '$file' is not using TLG Workplace's default Greek encoding.<br>
      Please do the following:
      <ul>
        <li>Save your TLG Workplace search (File > Save As).
        <li>Uncheck all TLG Workplace font options (Setup > Preferences > Language Display).
        <li>Open your TLG Workplace search (File > Save As).
        <li>Save your TLG Workplace search results (File > Save Results as RTF File).
      </ul>
HTML
		print $warning2;
		print $q->end_html;												# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
		exit;
	
	} else {
		
		print $warning1;
		print "      The format of the file named '$file' cannot be processed by QuotationFinder.\n"
			. "      Click <a href=\"/QuotationFinderHelp.html#Choose_File\" target=\"Help\">here</a> for further instructions.\n";
		print $warning2;
		print $q->end_html;												# Uses the end_html function from CGI.pm to print the ending HTML tags;
																		# CGI.pm 241, CGI 5.3 (103).
		exit;
	}
}																		# Closes the check_upload subroutine; Camel3 6.2, Cookbook 10.0.


sub print_files_searched {
	my ( $q, $id, $mo, $se, $en, $mt, $su ) = @_;											# Copies the values passed to the subroutine, contained in the @_ ar-
																		# ray, to the q and id private variables, respectively; Camel3 6.2.1, 
																		# CGI 11.2 (277).
	my $fileName;														# Declares private variables that exist only within innermost enclosing
	my $description;													# block; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.

	error( $q, "userDir is an empty string, I'm in sub print_files_searched." ) if ($userDir eq "");	# For debugging
	error( $q, "searchDir is an empty string, I'm in sub print_files_searched." ) if ($searchDir eq "");
	my $mldb = tie %textFiles, 'MLDBM', $mldbTextFiles, O_CREAT | O_RDWR, 0644 or error( $q, "Can't open tie to MLDBM file, I'm in print_files_searched: $!" );
																		# Associates the database file whose path is stored in the mldbText-
																		# Files variable with the textFiles hash so that, using the MLDBM mo-
																		# dule, any changes to the hash are saved to the file (which is created
																		# with write access for us but no one else in case it doesn't exist 
																		# yet); Cookbook 14.1, CGI 7.4 (191), 10.2 (241), DBI 2.7 (32), 2.9 
																		# (51), Cozens 435.
	undef $mldb;														# Frees up the memory associated with the object; Camel3 29.2.187, 
																		# Cookbook 11.0.
	
	if (scalar keys %textFiles < 1) {									# If the number of keys of the textFiles hash is less than 1, the fol-
																		# lowing block of code is executed; Camel3 2.9.
		error($q, "textFiles empty $!");								# Calls the error subroutine and passes it an error message; CGI 5.2 
																		# (99).
	}																	# Closes the if block; Nutshell 4.3.

	print $q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
			-title=>'Files Searched',									# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
			-head=>meta({-http_equiv=>'Content-Type',
				-content=>'text/html; charset=UTF-8'}),
			-style=>{-src=>"$quotationFinderCss"},
			-expires=>'-1d',
			-pragma=>'no-cache',
			-charset=>'UTF-8', 
		),
		$q->start_form;

	navigation_header( $q, $id, $mo, $se, $en, $mt, $su );												# Calls the navigation_header subroutine; Camel3 6.2, Cookbook 10.0.

	print <<HTML;
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
  <td>&nbsp;</td>
    <td> 
HTML

	if (scalar keys %textFiles == 1) {									# If the number of keys of the textFiles hash is equal to 1, the fol-
																		# lowing block of code is executed; Camel3 2.9.
		print <<HTML;
      <h5>File Searched</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr>
    <td>&nbsp;</td>
    <td class=roman>
      The following file has been searched so far:
HTML

	} else {															# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
		print <<HTML;
      <h5>Files Searched</h5>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td class=roman align="right"><a href="/quotationfinder/QuotationFinderHelp.html#Results" target="Help">Help&nbsp;</a></td>
    <td class=roman>
      The following files have been searched so far:
HTML

	}																	# Closes the if... else... block; Nutshell 4.3.

	print <<HTML;
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr>
    <td class=roman>&nbsp;</td>
    <td>
      <ul>
HTML

	foreach $fileName ( sort keys %textFiles ) {						# For each key of the textFiles hash, the following block of code is 
																		# executed with the keys sorted and their names passed to the fileName 
																		# variable; Cookbook 5.9, Camel3 4.4.3.
		print "<li>$fileName\n";											# Prints some HTML and the value of the fileName variable; CGI 5.4 
																		# (111).
		$description = $textFiles{$fileName};							# Gets the value of the textFiles hash that is stored under the file-
																		# Name variable key, and stores it in the description variable; Lear-
																		# ning 1.5.6.
		if ($description ne "") {										# If the value stored in the description variable is not an empty 
																		# string, the following block of code is executed; Nutshell 4.5.4.2.
			print "<br>$description";									# Prints some HTML and the value of the description variable; CGI 5.4 
																		# (111).
		}																# Closes the if block; Nutshell 4.3.
		print "</li>";													# Prints some HTML; CGI 5.4 (111).
 	}																	# Closes the foreach loop; Nutshell 4.3.
 	
	print <<HTML;
      </ul>
    </td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td>&nbsp;</td>
  </tr>
  <tr> 
    <td>&nbsp;</td>
    <td class=roman> 
      <input type="submit" name="viewNavigation" value="View Navigation Page">
    </td>
  </tr>
</table>
HTML

	print	$q->hidden(												# CGI 11.2 (278)
				-name     => "id",
				-default  => $id,
			),
			$q->hidden(
				-name     => "mo",
				-default  => $mo,
			),
			$q->hidden(
				-name     => "se",
				-default  => $se,
			),
			$q->hidden(
				-name     => "en",
				-default  => $en,
			),
			$q->hidden(
				-name     => "mt",
				-default  => $mt,
			),
			$q->hidden(
				-name     => "su",
				-default  => $su,
			),
 			$q->end_form, 												# Uses the end_form and end_html functions from CGI.pm to print the 
			$q->end_html;												# ending FORM and HTML tags; CGI.pm 241, CGI 5.3 (103).

	untie %textFiles;													# Closes $mldbTextFiles; Cookbook 14.1, CGI 10.2 (241).
}																		# Closes the print_files_searched subroutine; Camel3 6.2, Cookbook 


sub convert_string_to_unicode {
	my $string = shift;												# Stores the value passed to the subroutine in the string variable; 
																		# Camel3 29.2.149.
	my $newString;
	
	$string =~ s/([\?\.,:;'\-_\[\]])<\/span>/<\/span>$1/g;					# Takes the string stored in the string variable, substitutes every 
																		# occurrence of the pattern between the first set of slashes by the
																		# one between the second pairand stores the result back in the 
																		# string variable; Camel3 5.2.3. This moves punctuation marks outside
																		# the closing bold tags.
	my @chunks = split /(<span class=corematch>|<span class=match>|<\/span>)/, $string;		# Cookbook 6.7. We split off the tags from the  
	foreach $chunk (@chunks) {											# Greek words so that we can do the Unicode conversion more safely.
		if ($chunk eq " ") {
			$newString .= " ";
		} elsif ($chunk =~ /(<span class=corematch>|<span class=match>|<\/span>)/) {
			$newString .= "$1";
		} else {
			my $trailingWhitespace = $1 if ($chunk =~ /(\s+)$/);
			my @words = split /\s+/, $chunk;
			foreach my $word (@words) {
				$word =~ s/\\/ß/g;								# There are problems splitting strings on multiple-byte characters that contain backslashes. This is why we're
																	# replacing every occurrence of a backslash in a Beta Greek word with
																	# a German sharp s.
#					$word =~ s/([^*])S([\?\.,:;'\-_\[\]">])?$/$1S2$2/g;						# Takes the string stored in the word variable, substitutes the pat-
				$word =~ s/([^*])S([\W_]+)/$1S2$2/g;						# Takes the string stored in the word variable, substitutes the pat-
				$word =~ s/([^*])S$/$1S2/g;						# Takes the string stored in the word variable, substitutes the pat-
																				# tern between the first set of slashes by the one between the second
																				# set, and stores the result back in the word variable; Camel3 5.2.3.
																				# This replaces non-capital medial by final sigmas before whitespace 
																				# and punctuation marks.
				my @chars = split /($beta)/ox, $word;			# One character per list element; Camel3 29.2.161.
				for my $char (@chars) {
					next unless ($char);										# Skip the rest of the block unless the value stored in the char variable 
																				# is a true value, i.e. not an empty string; Cookbook 1.0.
					my $uni = $betaToUni{$char};
					my $punct = $punctuation{$char};
					my $font = $fontChanges{$char};
					my $pFormat = $pageFormatting{$char};
					my $mark = $markup{$char};
					my $quot = $quotationMarks{$char};
					my $tFormat = $textFormatting{$char};
					my $parenth = $parentheses{$char};
					my $addPunct = $addPunctuation{$char};
					my $addChar = $addCharacters{$char};
					if ($uni) {
						$char = $uni;
					} elsif ($punct) {
						$char = $punct;
					} elsif ($font) {
						$char = $font;
					} elsif ($pFormat) {
						$char = $pFormat;
					} elsif ($mark) {
						$char = $mark;
					} elsif ($quot) {
						$char = $quot;
					} elsif ($tFormat) {
						$char = $tFormat;
					} elsif ($parenth) {
						$char = $parenth;
					} elsif ($addPunct) {
						$char = $addChar;
					} elsif ($addChar) {
						$char = $addChar;
					} elsif ($char eq " ") {
						$char = " ";
					} else {
						## deal with unknown EUC->Unicode mapping here.
		#				print "no unicode for char $char in string $string<br>";
					}
				}
				$word = join("",@chars);
		#		$word =~ s/&sgr;(&SqBrR;)?$/&sfgr;\1/;			# Replaces trailing sigma by final sigma; Cookbook 1.14, Friedl 227.
		#		$word =~ s/C3;$/C2;/;												# Replaces trailing sigma by final sigma; Cookbook 1.14, Friedl 227.
			}
			$chunk = join(" ", @words);
			$chunk .= $trailingWhitespace;
			$newString .= $chunk;
		}
	}
	$string = $newString;
}																		# Closes the convert_string_to_unicode subroutine; Camel3 6.2, Cookbook 10.0.


sub convert_refTextChunk_to_unicode {

	my $chunkBeta = shift;													# Stores the value passed to the subroutine in the chunk variable; 
																		# Camel3 29.2.149.
	my @chars = split (//, $chunkBeta);										# Splits up the string stored in the wordBeta variable and puts the 
																		# characters in the chars array; Cookbook 1.5.
	for my $char (@chars) {
#	$testString .= $char;
		next unless ($char);											# Skip the rest of the block unless the value stored in the char variable 
																		# is a true value, i.e. not an empty string; Cookbook 1.0.
		my $uniChar = $betaToUni{$char};
		if ($uniChar) {													# Cookbook 1.0.
			$char = $uniChar;
		} else {
			$char = "";
		}
	}
	$chunk = join("",@chars);
	$chunk =~ s/C3;$/C2;/;												# Replaces trailing sigma by final sigma; Cookbook 1.14, Friedl 227.
	return $chunk;
}																		# Closes the convert_refTextChunk_to_unicode subroutine; Camel3 6.2, Cookbook 10.0.


sub convert_symbolgreek_to_beta {

	my $lineSygr = shift;													# Stores the value passed to the subroutine in the chunk variable; 
																		# Camel3 29.2.149.
	$lineSygr =~ s/\\/ß/g;												# There are problems splitting strings on multiple-byte characters 
																		# that contain backslashes. This is why we're replacing every occur-
																		# rence of a backslash in a Beta Greek word with a German sharp s.
	
	my @chars = split /($sygr)/ox, $lineSygr;			# One character per list element; Camel3 29.2.161.
#	my @chars = split //, $lineSygr;			# One character per list element; Camel3 29.2.161.
																		# characters in the chars array; Cookbook 1.5.
	for my $char (@chars) {
#	$testString .= $char;
		next unless ($char);											# Skip the rest of the block unless the value stored in the char variable 
																		# is a true value, i.e. not an empty string; Cookbook 1.0.
		my $betaChar = $sygrToBeta{$char};
		if (defined $betaChar) {													# Cookbook 1.0.
			$char = $betaChar;
		} else {
#			push(@appOut, "character \"$char\" not defined in sygrToEnts and punctuation hashes"); ## deal with unknown mapping here.
			print "\ncharacter '$char' not defined in sygrToBeta hash\n"; ## deal with unknown mapping here.
#		} else {
			$char = "";
		}
	}
	my $line = join("",@chars);
	$line =~ s/ß/\\/g;												# There are problems splitting strings on multiple-byte characters 
	return $line;
}																		# Closes the convert_refTextChunk_to_unicode subroutine; Camel3 6.2, Cookbook 10.0.


sub convert_sgkclassic_to_beta {

	my $lineSgk = shift;													# Stores the value passed to the subroutine in the chunk variable; 
																		# Camel3 29.2.149.
	$lineSgk =~ s/\\/ß/g;												# There are problems splitting strings on multiple-byte characters 
																		# that contain backslashes. This is why we're replacing every occur-
																		# rence of a backslash in a Beta Greek word with a German sharp s.
	
	my @chars = split /($sgk)/ox, $lineSgk;			# One character per list element; Camel3 29.2.161.
#	my @chars = split //, $lineSgk;			# One character per list element; Camel3 29.2.161.
																		# characters in the chars array; Cookbook 1.5.
	for my $char (@chars) {
#	$testString .= $char;
		next unless ($char);											# Skip the rest of the block unless the value stored in the char variable 
																		# is a true value, i.e. not an empty string; Cookbook 1.0.
		my $betaChar = $sgkToBeta{$char};
		if (defined $betaChar) {													# Cookbook 1.0.
			$char = $betaChar;
		} else {
#			push(@appOut, "character \"$char\" not defined in sygrToEnts and punctuation hashes"); ## deal with unknown mapping here.
#			print "character '$char' not defined in sgkToBeta hash<br>"; ## deal with unknown mapping here.
#		} else {
			$char = "";
		}
	}
	my $line = join("",@chars);
	$line =~ s/ß/\\/g;												# There are problems splitting strings on multiple-byte characters 
	return $line;
}																		# Closes the convert_refTextChunk_to_unicode subroutine; Camel3 6.2, Cookbook 10.0.


sub process_work_title {

	my $workProcessed;
	
	$work =~ s/&1(.+?)&/<i>$1<\/i>/g;					# SOLLTE EIGENTLICH FETT SEIN, ABER MEINE work ANGABEN SIND SCHON FETT.

	my @chunks = split /(\$.*?&)/, $work;
	
	foreach my $chunk (@chunks) {

		if ($chunk =~ /\$(.+?)&/) {
	
			$chunk = convert_string_to_unicode($1);	# Calls the convert_string_to_unicode subroutine, passes it the chunk va-
														# riable, and then passes the result of the subroutine back to the
														# chunk variable; Camel3 6.2.1.
#			print "<br>$chunk<br>";
			$workProcessed .= "<span class=greek>$chunk</span>";

		} else {
		
			$workProcessed .= $chunk;
		
		}
	}
	
	$work = $workProcessed;
	
	return $work;
}																		# Closes the convert_refTextChunk_to_unicode subroutine; Camel3 6.2, Cookbook 10.0.



# DIE FOLGENDEN BLÖCKE SIND VON CGI 11.2 (276). SIE SIND NOCH NICHT INTEGRIERT. WAS FÜR MICH JETZT WICHTIG IST, IST NICHT DAS SPEICHERN IRGEND-
# WELCHER PARAMETER, SONDERN DASS MIT tie DIE BEREITS BESTEHENDEN HASHES EINGELESEN WERDEN, WO ZU $id (VORMALS $userPass) DIE userDirS UND DAZU
# WIEDER DIE searchDirS GESPEICHERT SIND.

# FALLS DER FLOW CONTROL IMMER NOCH MÜHE MACHT: WIE WÄR'S, WENN MAN GEMÄSS DER ERKLÄRUNG ZU param IN CGI.PM EINFACH SAGEN WÜRDE: unless param
# { print_login( $q ) }; ?

# Reads a saved CGI object from disk and return its params as a hash ref
sub get_id {															# Begins the get_id subroutine; Camel3 6.2, Cookbook 10.0. This subrou-
																		# tine gets an id, either from a query string or as a hidden field in a
																		# form submitted via POST.
	my $q = shift;														# Shifts the first value off the @_ array (containing the values passed
    																	# to the subroutine) and stores it in a private variable named q; Ca-
    																	# mel3 29.2.149.
#	my $id;																# Declares private variables that exist only within the innermost en-
    																	# closing subroutine; Camel3 2.5., 4, 29.2.99, Cookbook 10.2.
	my $unsafe_id = $q->param( "id" ) || '';							# Gets the value of the id parameter (or an empty string, if there is 
    																	# no such parameter) and stores it in a private variable named un- 
    																	# safe_id; CGI.pm 5.4 (232), CGI 11.2 (282). The parameter can come 
    																	# from a query string or a hidden field.
	$unsafe_id =~ s/[^\dA-Fa-f]//g;										# Substitutes anything other than digits and letters a-f (either upper 
																		# or lower case) in the string stored in the unsafe_id variable with 
																		# nothing; Friedl 1.4.2 (10), 7.3.6 (240)
	if ( $unsafe_id =~ /^(.+)$/ ) {										# If the string stored in the unsafe_id variable contains any (one or 
																		# more) characters (between its beginning and its end), they get stored
																		# in the $1 variable and the following block of code is executed; 
																		# Friedl 1.4.1 (8), 1.4.3 (11), 1.4.8 (17).
		$id = $1;														# Assigns the value of the $1 to the id variable; Camel3 1.5.3.
error( $q, "q is $q, id is $id, userDir is $userDir." );
#		load_state( $q, $id );											# Calls the load_state subroutine, passing it the q and id variables;
																		# Camel3 6.2.
	}																	# Closes the if block; Nutshell 4.3.
	else {																# If the above condition is not met, the following block of code is 
																		# executed; Camel3 1.6.1.1.
 #		$id = unique_id();												# Calls the unique_id subroutine and stores the returned value in the 
 																		# variable named id; Camel3 6.2.
		$q->param( -name => "start", -value => "start" );
 #		$q->param( -name => "id", -value => $id );						# Sets a parameter named id, containing the value of the id variable; 
 																		# CGI 5.2 (94).
	}																	# Closes the else block; Nutshell 4.3.
	return $id;															# Causes the subroutine to return immediately with the id variable's 
																		# value; Camel3 29.2.131.
}																		# Closes the get_id subroutine; Camel3 6.2, Cookbook 10.0.


# Loads the current CGI object's default parameters from the saved state
sub load_state {
    my( $q, $id ) = @_;
    my $saved = get_state( $id ) or return;
    
    foreach ( $saved->param ) {
        $q->param( $_ => $saved->param($_) ) unless defined $q->param($_);
    }
}


sub get_state {
    my $id = shift;
    my $cart = cart_filename( $id );
    local *FILE;
    
    -e $cart or return;
    open FILE, $cart or die "Cannot open $cart: $!";
    my $q_saved = new CGI( \*FILE ) or
        error( $q, "Unable to restore saved state." );
    close FILE;
    
    return $q_saved;
}


# Saves the current CGI object to disk
sub save_state {
    my $q = shift;
    my $cart = cart_filename( $id );
    local( *FILE, *DIR );
    
    # Avoid DoS attacks by limiting the number of data files
    my $num_files = 0;
#    opendir DIR, $DATA_DIR;
    $num_files++ while readdir DIR;
    closedir DIR;
    
    # Compare the file count against the max
#    if ( $num_files > $MAX_FILES ) {
        error( $q, "We cannot save your request because the directory " .
                   "is full. Please try again later" );
#    }
    
    # Save the current CGI object to disk
#    open FILE, "> $cart" or return die "Cannot write to $cart: $!";
    $q->save( \*FILE );
    close FILE;
}


# Returns a list of item titles and quantities
sub get_items {
    my $q = shift;
    my @items;
    
    # Build a sorted list of movie titles and quantities
    foreach ( $q->param ) {
        my( $title, $quantity ) = ( $_, $q->param( $_ ) );
        
        # Skip "* " from beginning of movie titles; skip other keys
        $title =~ s/^\*\s+// or next;
        $quantity or next;
        
        push @items, [ $title, $quantity ];
    }
    return @items;
}


# Separated from other code in case this changes in the future
sub cart_filename {
    my $id = shift;
#    return "$DATA_DIR/$id";
}


sub unique_id {
    # Use Apache's mod_unique_id if available
    return $ENV{UNIQUE_ID} if exists $ENV{UNIQUE_ID};
    
#    require Digest::MD5;
    
#    my $md5 = new Digest::MD5;
    my $remote = $ENV{REMOTE_ADDR} . $ENV{REMOTE_PORT};
    
    # Note this is intended to be unique, and not unguessable
    # It should not be used for generating keys to sensitive data
#    my $id = $md5->md5_base64( time, $$, $remote );
    $id =~ tr|+/=|-_.|;  # Make non-word chars URL-friendly
    return $id;
}






sub error {																# Begins the error subroutine; Camel3 6.2, Cookbook 10.0. This sub-
																		# routine displays error messages to the user.
    my( $q, $errorMessage ) = @_;										# Stores elements from the @_ array (containing the values passed to 
																		# the subroutine) in the q and errorMessage variables; Camel3 29.2.149,
																		# CGI 5.5 (117).
#	print	$q->header( "text/html" ),									# Prints the error message to the user's browser window, using CGI.pm
	print	$q->header(-expires=>'-1d',
				-charset=>'UTF-8'),
#			$q->start_html ( "Error" ),									# in object oriented mode; CGI.pm 3.6 (130).
			$q->start_html(												# Uses the start_html and start_form functions from CGI.pm to print the
				-title=>'Error',											# starting HTML and FORM tags; CGI.pm 253, 255, CGI 5.3 (110). 
				-head=>meta({-http_equiv=>'Content-Type',
					-content=>'text/html; charset=UTF-8'}),
				-style=>{-src=>"$quotationFinderCss"},
				-expires=>'-1d',
				-pragma=>'no-cache',
				-charset=>'UTF-8', 
			),
			$q->h1( "Error" ),
			$q->p( "Sorry, the following error has occurred: " ),
			$q->p( $q->i( $errorMessage ) ),
			$q->end_html;
	exit;																# Exits the program; Camel3 29.2.35.
}																		# Closes the error subroutine; Camel3 6.2, Cookbook 10.0.



# sub mbytes { $_[0] / (1024**2) }									# For debugging; MacPerl 193.


																		# Erklärung looping von multidimensionalen arrays: Camel 4.6.3 (Slices:
																		# 4.6.4), 4.7; Advanced 2.2; Cookbook 11.2.
																		# Looping von Hashes of arrays: Camel 4.7.2.3, Cookbook 11.2. Vgl. 
																		# Cookbook 5.4. und Camel 8.3.2.
																		# Neu zu Multidimensionalem: Camel3 9.

	# A WAY TO MAKE THE POSITION SCORE MORE ACCURATE WOULD BE TO FIRST DO ALL OTHER CALCULATIONS AND THEN DETERMINE THE AVERAGE POSI-
	# TION OF MATCHES BY FAVORING THE MATCHES THAT HAVE A HIGH SCORE ON OTHER COUNTS. 
	

# [$@%]xxxx[,; +-\{})] = regex for cleaning up "my" declarations.

# Apache error log on Mac OS X: ./private/var/log/httpd/error_log
# To see current log in the Terminal:
# - cd to root level (type "cd.." and hit return, then repeat)
# - type "tail -f ./private/var/log/httpd/error_log" and hit return