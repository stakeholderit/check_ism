#!/usr/bin/perl
#
# Nagios plugin
#
# Monitor Dell server hardware status using Dell iDRAC Service Module (iSM) via SNMP.
#
# Known caveats (current as of v0.0.1-beta) are as follows:
#  * Logic surrounding the battery check is not updated to reflect the "new" battery status that iSM exposes
#    where learnstate is not available.
#  * The plugin does not check for the presence of the iDRAC card itself, if the iSM service is running on
#    the host or if the SNMP agent is enabled in the iDRAC settings.
#  * There are probably leftovers from old support for Dell OpenManage Server Administrator (OMSA) that are
#    not used, but still not removed.
#  * The plugin does not check for any new OIDs that iSM might expose - it performs the same checks (if
#    still available) that the original check_openmanage plugin did.
#  * The plugin has been rewritten from the original check_openmanage plugin up against a PowerEdge R760
#    connected to an PowerVault MD2460 via a PERC12 H965e controller (and the PERC12 H965e is never going to
#    be supported by OMSA - the H965i is, but that's another story..), so we were forced to rewrite it for
#    iSM otherwise we would be unable to get metrics about the H965e, the MD2460 shelf and the disks it
#    contains.
#
#    It has not been tested on any other hardware yet, but please report back - especially if it works.
#
#    No special OIDs for this particular hardware has been added, so it should work on any Dell server with
#    iSM, but it might be, that some OIDs are not available on all hardware.
#
# Copyright (C) 2008-2017 Trond H. Amundsen
# Copyright (C) 2025 Jens Dueholm Christensen
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#

require 5.006; # Perl v5.6.0 or newer is required
use strict;
use warnings;
use POSIX qw(isatty ceil strtol);
use Getopt::Long qw(:config no_ignore_case);
use Sys::Hostname;

# Global (package) variables used throughout the code
use vars qw($NAME $ORG_NAME $VERSION $AUTHOR $CONTACT $ORG_AUTHOR $ORG_CONTACT $E_OK $E_WARNING $E_CRITICAL
	$E_UNKNOWN $USAGE $HELP $LICENSE
	$snmp_session $snmp_error $globalstatus $global
	$linebreak $omopt_chassis $omopt_system $blade
	$exit_code $snmp
	%check %opt %reverse_exitcode %status2nagios %country
	%snmp_status %snmp_probestatus %probestatus2nagios %sysinfo
	%blacklist %nagios_alert_count %count %snmp_enclosure %snmp_controller
	@perl_warnings @controllers @enclosures @perfdata
	@report_storage @report_chassis @report_other
);

#---------------------------------------------------------------------
# Initialization and global variables
#---------------------------------------------------------------------

# Collect perl warnings in an array
$SIG{__WARN__} = sub {push @perl_warnings, [ @_ ];};

# Version and similar info
$NAME = 'check_ism';
$ORG_NAME = 'check_openmanage';
$VERSION = '0.0.1-beta';
$AUTHOR = 'Jens Dueholm Christensen';
$ORG_AUTHOR = 'Trond H. Amundsen';
$CONTACT = 'jedc@ramboll.com';
$ORG_CONTACT = 't.h.amundsen@usit.uio.no';

# Exit codes
$E_OK = 0;
$E_WARNING = 1;
$E_CRITICAL = 2;
$E_UNKNOWN = 3;

# Usage text
$USAGE = <<"END_USAGE";
Usage: $NAME [OPTION]...
END_USAGE

# Help text
$HELP = <<'END_HELP';

GENERAL OPTIONS:

   -f, --config         Specify configuration file
   -p, --perfdata       Output performance data [default=no]
   -t, --timeout        Plugin timeout in seconds [default=30]
   -c, --critical       Custom temperature critical limits
   -w, --warning        Custom temperature warning limits
   -F, --fahrenheit     Use Fahrenheit as temperature unit
   -d, --debug          Debug output, reports everything
   -h, --help           Display this help text
   -V, --version        Display version info

SNMP OPTIONS:

   -H, --hostname       Hostname or IP (always required)
   -C, --community      SNMP community string [default=public]
   -P, --protocol       SNMP protocol version [default=2c]
   --port               SNMP port number [default=161]
   -6, --ipv6           Use IPv6 instead of IPv4 [default=no]
   --tcp                Use TCP instead of UDP [default=no]

OUTPUT OPTIONS:

   -i, --info           Prefix any alerts with the service tag
   -e, --extinfo        Append system info to alerts
   -s, --state          Prefix alerts with alert state
   -S, --short-state    Prefix alerts with alert state abbreviated
   -o, --okinfo         Verbosity when check result is OK
   -B, --show-blacklist Show blacklistings in OK output
   -I, --htmlinfo       HTML output with clickable links

CHECK CONTROL AND BLACKLISTING:

   -a, --all            Check everything, even log content
   -b, --blacklist      Blacklist missing and/or failed components
   --only               Only check a certain component or alert type
   --check              Fine-tune which components are checked
   --no-storage         Don't check storage
   --vdisk-critical     Make any alerts on virtual disks critical

For more information and advanced options, see the manual page or URL:
  https://github.com/trondham/check_openmanage
  https://github.com/stakeholderit/check_ism
END_HELP

# Version and license text
$LICENSE = <<"END_LICENSE";
$NAME $VERSION
Copyright (C) 2008-2017 $ORG_AUTHOR
Copyright (C) 2025 $AUTHOR
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.

Written by $ORG_AUTHOR <$ORG_CONTACT> as $ORG_NAME
Modified by $AUTHOR <$CONTACT> for iSM and pure SNMP monitoring as $NAME
END_LICENSE

# Options with default values
%opt = (
	'blacklist'       => [],       # blacklisting
	'check'           => [],       # check control
	'critical'        => [],       # temperature critical limits
	'warning'         => [],       # temperature warning limits
	'tempunit'        => 'C',      # temperature unit
	'fahrenheit'      => 0,        # Use fahrenheit
	'configfile'      => undef,    # configuration file
	'timeout'         => 30,       # default timeout is 30 seconds
	'snmp_timeout'    => 5,        # SNMP transport layer timeout
	'debug'           => 0,        # debugging / verbose output
	'help'            => 0,        # display help output
	'perfdata'        => undef,    # output performance data
	'legacy_perfdata' => 0,        # legacy performance data output
	'info'            => 0,        # display servicetag
	'extinfo'         => 0,        # display extra info
	'htmlinfo'        => undef,    # html tags in output
	'postmsg'         => undef,    # post message
	'state'           => 0,        # display alert type
	'short-state'     => 0,        # display alert type (short)
	'okinfo'          => 0,        # default "ok" output level
	'show_blacklist'  => 0,        # show blacklisted components
	'linebreak'       => undef,    # specify linebreak
	'version'         => 0,        # plugin version info
	'all'             => 0,        # check everything
	'only'            => undef,    # only one component
	'no_storage'      => 0,        # don't check storage
	'port'            => 161,      # default SNMP port
	'hostname'        => undef,    # hostname or IP
	'community'       => 'public', # SMNP v1 or v2c
	'protocol'        => '2c',     # default SNMP protocol 2c
	'ipv6'            => 0,        # default is IPv4
	'tcp'             => 0,        # default is UDP
	'username'        => undef,    # SMNP v3
	'authpassword'    => undef,    # SMNP v3
	'authkey'         => undef,    # SMNP v3
	'authprotocol'    => undef,    # SMNP v3
	'privpassword'    => undef,    # SMNP v3
	'privkey'         => undef,    # SMNP v3
	'privprotocol'    => undef,    # SMNP v3
	'use_get_table'   => 0,        # hack for SNMPv3 on Windows with net-snmp
	'hide_servicetag' => 0,        # hidden servicetag
	'vdisk_critical'  => 0,        # make vdisk alerts critical
	'maxMsgSize'      => 65535,    # Max SNMP octetsize
);

# Get options
GetOptions('b|blacklist=s' => \@{$opt{blacklist}},
	'check=s'              => \@{$opt{check}},
	'c|critical=s'         => \@{$opt{critical}},
	'w|warning=s'          => \@{$opt{warning}},
	'tempunit=s'           => \$opt{tempunit},
	'F|fahrenheit'         => \$opt{fahrenheit},
	'f|config=s'           => \$opt{configfile},
	't|timeout=i'          => \$opt{timeout},
	'snmp-timeout=i'       => \$opt{snmp_timeout},
	'd|debug'              => \$opt{debug},
	'h|help'               => \$opt{help},
	'V|version'            => \$opt{version},
	'p|perfdata:s'         => \$opt{perfdata},
	'legacy-perfdata'      => \$opt{legacy_perfdata},
	'i|info'               => \$opt{info},
	'e|extinfo'            => \$opt{extinfo},
	'I|htmlinfo:s'         => \$opt{htmlinfo},
	'postmsg=s'            => \$opt{postmsg},
	's|state'              => \$opt{state},
	'S|short-state'        => \$opt{shortstate},
	'o|ok-info=i'          => \$opt{okinfo},
	'B|show-blacklist'     => \$opt{show_blacklist},
	'linebreak=s'          => \$opt{linebreak},
	'a|all'                => \$opt{all},
	'only=s'               => \$opt{only},
	'no-storage'           => \$opt{no_storage},
	'port=i'               => \$opt{port},
	'H|hostname=s'         => \$opt{hostname},
	'C|community=s'        => \$opt{community},
	'P|protocol=s'         => \$opt{protocol},
	'6|ipv6'               => \$opt{ipv6},
	'tcp'                  => \$opt{tcp},
	'U|username=s'         => \$opt{username},
	'authpassword=s'       => \$opt{authpassword},
	'authkey=s'            => \$opt{authkey},
	'authprotocol=s'       => \$opt{authprotocol},
	'privpassword=s'       => \$opt{privpassword},
	'privkey=s'            => \$opt{privkey},
	'privprotocol=s'       => \$opt{privprotocol},
	'use-get_table'        => \$opt{use_get_table},
	'hide-servicetag'      => \$opt{hide_servicetag},
	'vdisk-critical'       => \$opt{vdisk_critical},
) or do {
	print $USAGE;
	exit $E_UNKNOWN
};

# If user requested help
if ($opt{help}) {
	print $USAGE, $HELP;
	exit $E_UNKNOWN;
}

# If user requested version info
if ($opt{version}) {
	print $LICENSE;
	exit $E_UNKNOWN;
}

# Initialize blacklist
%blacklist = ();

# Check flags, override available with the --check option
%check = ('storage' => 1, # check storage subsystem
	'memory'        => 1, # check memory (dimms)
	'fans'          => 1, # check fan status
	'power'         => 1, # check power supplies
	'temp'          => 1, # check temperature
	'cpu'           => 1, # check processors
	'voltage'       => 1, # check voltage
	'batteries'     => 1, # check battery probes
	'amperage'      => 1, # check power consumption
	'intrusion'     => 1, # check intrusion detection
	'sdcard'        => 1, # check removable flash media (SD cards)
	'alertlog'      => 0, # check the alert log
	'esmlog'        => 0, # check the ESM log (hardware log)
	'servicetag'    => 1, # check that the servicetag is sane
);

# Messages
@report_storage = (); # messages with associated nagios level (storage)
@report_chassis = (); # messages with associated nagios level (chassis)
@report_other = ();   # messages with associated nagios level (other)

# Read config file
parse_configfile() if defined $opt{configfile};

# Setting timeout
$SIG{ALRM} = sub {
	print "PLUGIN TIMEOUT: $NAME timed out after $opt{timeout} seconds\n";
	exit $E_UNKNOWN;
};
alarm $opt{timeout};

# If we're using SNMP
$snmp = defined $opt{hostname} ? 1 : 0;

# SNMP session variables
$snmp_session = undef;
$snmp_error = undef;

# Default line break
$linebreak = isatty(*STDOUT) ? "\n" : '<br/>';

# Line break from option
if (defined $opt{linebreak}) {
	if ($opt{linebreak} eq 'REG') {
		$linebreak = "\n";
	}
	elsif ($opt{linebreak} eq 'HTML') {
		$linebreak = '<br/>';
	}
	else {
		$linebreak = $opt{linebreak};
	}
}

# List of controllers and enclosures
@controllers = ();    # controllers
@enclosures = ();     # enclosures
%snmp_enclosure = (); # enclosures

# Counters for everything
%count
	= (
	'pdisk' => 0, # number of physical disks
	'vdisk' => 0, # number of logical drives (virtual disks)
	'temp'  => 0, # number of temperature probes
	'volt'  => 0, # number of voltage probes
	'amp'   => 0, # number of amperage probes
	'intr'  => 0, # number of intrusion probes
	'dimm'  => 0, # number of memory modules
	'mem'   => 0, # total memory
	'fan'   => 0, # number of fan probes
	'cpu'   => 0, # number of CPUs
	'bat'   => 0, # number of batteries
	'power' => 0, # number of power supplies
	'sd'    => 0, # number of SD cards
	'esm'   => {
		'Critical'     => 0, # critical entries in ESM log
		'Non-Critical' => 0, # warning entries in ESM log
		'Ok'           => 0, # ok entries in ESM log
	},
	'alert' => {
		'Critical'     => 0, # critical entries in alert log
		'Non-Critical' => 0, # warning entries in alert log
		'Ok'           => 0, # ok entries in alert log
	},
);

# Performance data
@perfdata = ();

# Global health status
$global = 1;           # default is to check global status
$globalstatus = $E_OK; # default global health status is "OK"

# Nagios error levels reversed
%reverse_exitcode
	= (
	$E_OK       => 'OK',
	$E_WARNING  => 'WARNING',
	$E_CRITICAL => 'CRITICAL',
	$E_UNKNOWN  => 'UNKNOWN',
);

# iSM and SNMP error levels
%status2nagios
	= (
	'Unknown'         => $E_CRITICAL,
	'Critical'        => $E_CRITICAL,
	'Non-Critical'    => $E_WARNING,
	'Ok'              => $E_OK,
	'Non-Recoverable' => $E_CRITICAL,
	'Other'           => $E_CRITICAL,
);

# Status via SNMP
%snmp_status
	= (
	1 => 'Other',
	2 => 'Unknown',
	3 => 'Ok',
	4 => 'Non-Critical',
	5 => 'Critical',
	6 => 'Non-Recoverable',
);

# Probe Status via SNMP
%snmp_probestatus
	= (
	1  => 'Other',               # probe status is not one of the following:
	2  => 'Unknown',             # probe status is unknown (not known or monitored)
	3  => 'Ok',                  # probe is reporting a value within the thresholds
	4  => 'nonCriticalUpper',    # probe has crossed upper noncritical threshold
	5  => 'criticalUpper',       # probe has crossed upper critical threshold
	6  => 'nonRecoverableUpper', # probe has crossed upper non-recoverable threshold
	7  => 'nonCriticalLower',    # probe has crossed lower noncritical threshold
	8  => 'criticalLower',       # probe has crossed lower critical threshold
	9  => 'nonRecoverableLower', # probe has crossed lower non-recoverable threshold
	10 => 'failed',              # probe is not functional
);

# Probe status translated to Nagios alarm levels
%probestatus2nagios
	= (
	'Other'               => $E_CRITICAL,
	'Unknown'             => $E_CRITICAL,
	'Ok'                  => $E_OK,
	'nonCriticalUpper'    => $E_WARNING,
	'criticalUpper'       => $E_CRITICAL,
	'nonRecoverableUpper' => $E_CRITICAL,
	'nonCriticalLower'    => $E_WARNING,
	'criticalLower'       => $E_CRITICAL,
	'nonRecoverableLower' => $E_CRITICAL,
	'failed'              => $E_CRITICAL,
);

# System information gathered
%sysinfo
	= (
	'hostname'   => 'N/A', # hostname
	'bios'       => 'N/A', # BIOS version
	'biosdate'   => 'N/A', # BIOS release date
	'serial'     => 'N/A', # serial number (service tag)
	'express_sc' => 'N/A', # express service code
	'model'      => 'N/A', # system model
	'rev'        => q{},   # system revision
	'osname'     => 'N/A', # OS name
	'osver'      => 'N/A', # OS version
	'rac'        => 0,     # HAS remote access controller (RAC)
	'rac_name'   => 'N/A', # remote access controller (RAC)
	'rac_fw'     => 'N/A', # RAC firmware
);

# Country and language list for URL generation
%country
	= (
	# EMEA
	at => { c => 'at', l => 'de' }, # Austria
	be => { c => 'be', l => 'nl' }, # Belgium
	cz => { c => 'cz', l => 'cs' }, # Czech Republic
	de => { c => 'de', l => 'de' }, # Germany
	dk => { c => 'dk', l => 'da' }, # Denmark
	es => { c => 'es', l => 'es' }, # Spain
	fi => { c => 'fi', l => 'fi' }, # Finland
	fr => { c => 'fr', l => 'fr' }, # France
	gr => { c => 'gr', l => 'el' }, # Greece
	it => { c => 'it', l => 'it' }, # Italy
	il => { c => 'il', l => 'en' }, # Israel
	me => { c => 'me', l => 'en' }, # Middle East
	no => { c => 'no', l => 'no' }, # Norway
	nl => { c => 'nl', l => 'nl' }, # The Netherlands
	pl => { c => 'pl', l => 'pl' }, # Poland
	pt => { c => 'pt', l => 'pt' }, # Portugal
	ru => { c => 'ru', l => 'ru' }, # Russia
	se => { c => 'se', l => 'sv' }, # Sweden
	uk => { c => 'uk', l => 'en' }, # United Kingdom
	za => { c => 'za', l => 'en' }, # South Africa
	# America
	br => { c => 'br', l => 'pt' }, # Brazil
	ca => { c => 'ca', l => 'en' }, # Canada
	mx => { c => 'mx', l => 'es' }, # Mexico
	us => { c => 'us', l => 'en' }, # USA
	# Asia/Pacific
	au => { c => 'au', l => 'en' }, # Australia
	cn => { c => 'cn', l => 'zh' }, # China
	in => { c => 'in', l => 'en' }, # India
	jp => { c => 'jp', l => 'ja' }, # Japan
);

# Adjust which checks to perform
adjust_checks() if defined $opt{check};

# Blacklisted components
set_blacklist($opt{blacklist}) if defined $opt{blacklist};

# If blacklisting is in effect, don't check global health status
if (scalar keys %blacklist > 0) {
	$global = 0;
}

# Take into account new hardware and blades
$blade = 0; # if this is a blade system

# Some initializations and checking before we begin
if ($snmp) {
	snmp_initialize();   # initialize SNMP
	snmp_check();        # check that SNMP works
	snmp_detect_blade(); # detect blade via SNMP
}

# Temperature unit
if ($opt{fahrenheit}) {
	$opt{tempunit} = 'F';
}

# Check tempunit syntax
if ($opt{tempunit} !~ m{\A C|F|K|R \z}xms) {
	print "ERROR: Unknown temperature unit '$opt{tempunit}'\n";
	exit $E_UNKNOWN;
}

#---------------------------------------------------------------------
# Helper functions
#---------------------------------------------------------------------

# Make a regex from a glob pattern. Shamelessly stolen from Perl
# Cookbook chapter 6.9
sub glob2regex {
	my $globstr = shift;
	my %patmap
		= ('*' => '.*',
		'?'    => '.',
		'['    => '[',
		']'    => ']',
	);
	$globstr =~ s{(.)} { $patmap{$1} || "\Q$1" }ge;
	return '\A' . $globstr . '\z';
}

#
# Read config file
#
sub parse_configfile {
	our $tiny = undef;

	# Regexp for boolean values
	our $off = qr{\A (0|off|false) \s* \z}ixms;
	our $on = qr{\A (1|on|true) \s* \z}ixms;

	# Mapping between command line options and the corresponding
	# config file options
	our %opt2config
		= ('info'         => 'output_servicetag',
		'extinfo'         => 'output_sysinfo',
		'postmsg'         => 'output_post_message',
		'state'           => 'output_servicestate',
		'shortstate'      => 'output_servicestate_abbr',
		'show_blacklist'  => 'output_blacklist',
		'hide_servicetag' => 'output_hide_servicetag',
		'htmlinfo'        => 'output_html',
		'okinfo'          => 'output_ok_verbosity',
		'protocol'        => 'snmp_version',
		'community'       => 'snmp_community',
		'port'            => 'snmp_port',
		'ipv6'            => 'snmp_use_ipv6',
		'tcp'             => 'snmp_use_tcp',
		'warning'         => 'temp_threshold_warning',
		'critical'        => 'temp_threshold_critical',
		'all'             => 'check_everything',
		'perfdata'        => 'performance_data',
		'tempunit'        => 'temperature_unit',
		'timeout'         => 'timeout',
		'snmp_timeout'    => 'snmp_timeout',
		'blacklist'       => 'blacklist',
		'legacy_perfdata' => 'legacy_performance_data',
		'vdisk_critical'  => 'vdisk_critical',
	);

	# Load the perl module
	if (eval {
		require Config::Tiny;
		1
	}) {
		$tiny = Config::Tiny->new();
	}
	else {
		print "ERROR: Required perl module 'Config::Tiny' not found\n";
		exit $E_UNKNOWN;
	}

	# Read the config file
	$tiny = Config::Tiny->read($opt{configfile})
		or do {
		report('other', (sprintf q{Couldn't read configuration file: %s}, Config::Tiny->errstr()), $E_UNKNOWN);
		return;
	};

	# Syntax check
	foreach my $section (keys %{$tiny}) {
		KEYWORD:
		foreach my $keyword (keys %{$tiny->{$section}}) {
			next KEYWORD if $keyword eq 'check_everything';
			if ($keyword =~ m{\A check_(.+)}xms) {
				my $c = $1;
				foreach my $cl (keys %check) {
					next KEYWORD if $c eq $cl;
				}
			}
			else {
				LEGAL:
				foreach my $legal (keys %opt2config) {
					next KEYWORD if $keyword eq $opt2config{$legal};
				}
			}
			if ($section eq '_') {
				report('other', qq{CONFIG ERROR: In the global section: Unknown statement "$keyword"}, $E_UNKNOWN);
			}
			else {
				report('other', qq{CONFIG ERROR: Unknown statement "$keyword" in section "$section"}, $E_UNKNOWN);
			}
		}
	}

	# Adjust checks according to statements in the configuration file
	sub configfile_adjust_checks {
		my $keyword = shift;
		CHECK_CONFIG:
		foreach my $key (keys %check) {
			my $copt = join '_', 'check', $key;
			next CHECK_CONFIG if !defined $tiny->{$keyword}->{$copt} or $tiny->{$keyword}->{$copt} eq q{};
			if ($tiny->{$keyword}->{$copt} =~ m{$on}ixms) {
				$check{$key} = 1;
			}
			elsif ($tiny->{$keyword}->{$copt} =~ m{$off}ixms) {
				$check{$key} = 0;
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for '$copt' must be boolean (True/False)", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set blacklist according to statements in the configuration file
	sub configfile_set_blacklist {
		my $keyword = shift;
		if (defined $tiny->{$keyword}->{blacklist} and $tiny->{$keyword}->{blacklist} ne q{}) {
			# set_blacklist() takes an array ref
			set_blacklist([ $tiny->{$keyword}->{blacklist} ]);
		}
		return;
	}

	# Set timeout according to statements in the configuration file
	sub configfile_set_timeout {
		my $keyword = shift;
		if (defined $tiny->{$keyword}->{timeout} and $tiny->{$keyword}->{timeout} ne q{}) {
			if ($tiny->{$keyword}->{timeout} =~ m{\A \d+ \z}xms) { # integer
				$opt{timeout} = $tiny->{$keyword}->{timeout};
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for 'timeout' must be a positive integer", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set SNMP timeout according to statements in the configuration file
	sub configfile_set_snmp_timeout {
		my $keyword = shift;
		if (defined $tiny->{$keyword}->{snmp_timeout} and $tiny->{$keyword}->{snmp_timeout} ne q{}) {
			if ($tiny->{$keyword}->{snmp_timeout} =~ m{\A \d+ \z}xms) { # integer
				$opt{snmp_timeout} = $tiny->{$keyword}->{snmp_timeout};
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for 'snmp_timeout' must be a positive integer", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set a boolean option
	sub configfile_set_boolean {
		my ($keyword, $bool) = @_;
		my $cbool = $opt2config{$bool};
		if (defined $tiny->{$keyword}->{$cbool} and $tiny->{$keyword}->{$cbool} ne q{}) {
			if ($tiny->{$keyword}->{$cbool} =~ m{$on}ixms) {
				$opt{$bool} = 1;
			}
			elsif ($tiny->{$keyword}->{$cbool} =~ m{$off}ixms) {
				$opt{$bool} = 0;
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for '$cbool' must be boolean (True/False)", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set htmlinfo option from config file
	sub configfile_set_htmlinfo {
		my $keyword = shift;
		my $conf = $opt2config{htmlinfo};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			if ($tiny->{$keyword}->{$conf} =~ m{$on}ixms) {
				$opt{htmlinfo} = 1;
			}
			elsif ($tiny->{$keyword}->{$conf} =~ m{$off}ixms) {
				$opt{htmlinfo} = undef;
			}
			else {
				$opt{htmlinfo} = $tiny->{$keyword}->{$conf};
			}
		}
		return;
	}

	# Set OK output verbosity
	sub configfile_set_ok_verbosity {
		my $keyword = shift;
		my $conf = $opt2config{okinfo};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			if ($tiny->{$keyword}->{$conf} =~ m{\A \d+ \z}xms) {
				$opt{okinfo} = $tiny->{$keyword}->{$conf};
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for '$conf' must be a positive integer", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set SNMP protocol version from config file
	sub configfile_set_snmp_version {
		my $keyword = shift;
		my $conf = $opt2config{protocol};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			if ($tiny->{$keyword}->{$conf} =~ m{\A (1|2(?:c)?|3) \z}xms) {
				$opt{protocol} = $tiny->{$keyword}->{$conf};
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for '$conf' must be '1', '2', '2c' or '3'", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set SNMP community name from config file
	sub configfile_set_snmp_community {
		my $keyword = shift;
		my $conf = $opt2config{community};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			$opt{community} = $tiny->{$keyword}->{$conf};
		}
		return;
	}

	# Set SNMP port number from config file
	sub configfile_set_snmp_port {
		my $keyword = shift;
		my $conf = $opt2config{port};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			if ($tiny->{$keyword}->{$conf} =~ m{\A \d+ \z}xms) { # integer
				$opt{port} = $tiny->{$keyword}->{$conf};
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for '$conf' must be a positive integer", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set temperature threshold from config file
	sub configfile_set_temp_threshold {
		my $keyword = shift;
		my $level = shift;
		my $conf = $opt2config{$level};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			$opt{$level} = [ $tiny->{$keyword}->{$conf} ]; # array ref
		}
		return;
	}

	# Set perfdata from config file
	sub configfile_set_perfdata {
		my $keyword = shift;
		my $conf = $opt2config{perfdata};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			if ($tiny->{$keyword}->{$conf} =~ m{$on}ixms) {
				$opt{perfdata} = 1;
			}
			elsif ($tiny->{$keyword}->{$conf} =~ m{$off}ixms) {
				$opt{perfdata} = undef;
			}
			elsif ($tiny->{$keyword}->{$conf} =~ m{\A minimal|multiline \z}xms) {
				$opt{perfdata} = $tiny->{$keyword}->{$conf};
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for '$conf' must be either boolean, 'minimal' or 'multiline'", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set temp unit from config file
	sub configfile_set_tempunit {
		my $keyword = shift;
		my $conf = $opt2config{tempunit};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			if ($tiny->{$keyword}->{$conf} =~ m{\A C|F|K|R \z}ixms) {
				$opt{tempunit} = $tiny->{$keyword}->{$conf};
			}
			else {
				report('other', "CONFIG ERROR: Rvalue for '$conf' must one of C/F/K/R", $E_UNKNOWN);
			}
		}
		return;
	}

	# Set postmsg string from config file
	sub configfile_set_postmsg {
		my $keyword = shift;
		my $conf = $opt2config{postmsg};
		if (defined $tiny->{$keyword}->{$conf} and $tiny->{$keyword}->{$conf} ne q{}) {
			$opt{postmsg} = $tiny->{$keyword}->{$conf}; # array ref
		}
		return;
	}

	# Sections in the config file to check for statements
	my @sections = ();

	# First: Populate the sections array with the global section
	@sections = ('_');

	# Last two steps only if hostname is defined
	if (defined $opt{hostname}) {
		# Second: Populate the sections array with host glob pattern (but
		# not exact match)
		PATTERN:
		foreach my $glob (sort keys %{$tiny}) {
			next PATTERN if $glob eq '_';            # global section
			next PATTERN if $glob eq $opt{hostname}; # exact match
			my $regex = glob2regex($glob);           # make regexp
			if ($opt{hostname} =~ m{$regex}) {
				push @sections, $glob;
			}
		}

		# Third: Populate the sections array with exact hostname
		if (defined $tiny->{$opt{hostname}}) {
			push @sections, $opt{hostname};
		}
	}

	# Loop through the sections array and get options
	foreach my $sect (@sections) {
		configfile_adjust_checks($sect);
		configfile_set_blacklist($sect);
		configfile_set_timeout($sect);
		configfile_set_snmp_timeout($sect);
		configfile_set_htmlinfo($sect);
		configfile_set_ok_verbosity($sect);
		configfile_set_boolean($sect, 'all');
		configfile_set_boolean($sect, 'info');
		configfile_set_boolean($sect, 'extinfo');
		configfile_set_boolean($sect, 'state');
		configfile_set_boolean($sect, 'shortstate');
		configfile_set_boolean($sect, 'show_blacklist');
		configfile_set_boolean($sect, 'ipv6');
		configfile_set_boolean($sect, 'tcp');
		configfile_set_boolean($sect, 'legacy_perfdata');
		configfile_set_boolean($sect, 'hide_servicetag');
		configfile_set_boolean($sect, 'vdisk_critical');
		configfile_set_snmp_version($sect);
		configfile_set_snmp_community($sect);
		configfile_set_snmp_port($sect);
		configfile_set_temp_threshold($sect, 'warning');
		configfile_set_temp_threshold($sect, 'critical');
		configfile_set_perfdata($sect);
		configfile_set_tempunit($sect);
		configfile_set_postmsg($sect);
	}

	return;
}

#
# Store a message in one of the message arrays
#
sub report {
	my ($type, $msg, $exval, $id) = @_;
	defined $id or $id = q{};

	my %type2array
		= (
		'storage' => \@report_storage,
		'chassis' => \@report_chassis,
		'other'   => \@report_other,
	);

	return push @{$type2array{$type}}, [ $msg, $exval, $id ];
}

#
# Initialize SNMP
#
sub snmp_initialize {
	# Legal SNMP v3 protocols
	my $snmp_v3_privprotocol = qr{\A des|aes|aes128|3des|3desde \z}xms;
	my $snmp_v3_authprotocol = qr{\A md5|sha \z}xms;

	# Parameters to Net::SNMP->session()
	my %param
		= (
		'-port'     => $opt{port},
		'-hostname' => $opt{hostname},
		'-version'  => $opt{protocol},
		'-timeout'  => $opt{snmp_timeout},
		# no longer needed after everything was moved to iSM?
		#	 '-maxMsgSize' => $opt{maxMsgSize},
	);

	# Setting the domain (IP version and transport protocol)
	my $transport = $opt{tcp} ? 'tcp' : 'udp';
	my $ipversion = $opt{ipv6} ? 'ipv6' : 'ipv4';
	$param{'-domain'} = "$transport/$ipversion";

	# Parameters for SNMP v3
	if ($opt{protocol} eq '3') {

		# Username is mandatory
		if (defined $opt{username}) {
			$param{'-username'} = $opt{username};
		}
		else {
			print "SNMP ERROR: With SNMPv3 a username must be specified\n";
			exit $E_UNKNOWN;
		}

		# Authpassword is optional
		if (defined $opt{authpassword}) {
			$param{'-authpassword'} = $opt{authpassword};
		}

		# Authkey is optional
		if (defined $opt{authkey}) {
			$param{'-authkey'} = $opt{authkey};
		}

		# Privpassword is optional
		if (defined $opt{privpassword}) {
			$param{'-privpassword'} = $opt{privpassword};
		}

		# Privkey is optional
		if (defined $opt{privkey}) {
			$param{'-privkey'} = $opt{privkey};
		}

		# Privprotocol is optional
		if (defined $opt{privprotocol}) {
			if ($opt{privprotocol} =~ m/$snmp_v3_privprotocol/xms) {
				$param{'-privprotocol'} = $opt{privprotocol};
			}
			else {
				print "SNMP ERROR: Unknown or invalid privprotocol [$opt{privprotocol}], "
					. "must be one of [des|aes|aes128|3des|3desde]\n";
				exit $E_UNKNOWN;
			}
		}

		# Authprotocol is optional
		if (defined $opt{authprotocol}) {
			if ($opt{authprotocol} =~ m/$snmp_v3_authprotocol/xms) {
				$param{'-authprotocol'} = $opt{authprotocol};
			}
			else {
				print "SNMP ERROR: Unknown or invalid authprotocol [$opt{authprotocol}], "
					. "must be one of [md5|sha]\n";
				exit $E_UNKNOWN;
			}
		}
	}
	# Parameters for SNMP v2c or v1
	elsif ($opt{protocol} =~ m{\A (1|2(?:c)?) \z}xms) {
		$param{'-community'} = $opt{community};
	}
	else {
		print "SNMP ERROR: Unknown or invalid SNMP version [$opt{protocol}]\n";
		exit $E_UNKNOWN;
	}

	# Try to initialize the SNMP session
	if (eval {
		require Net::SNMP;
		1
	}) {
		($snmp_session, $snmp_error) = Net::SNMP->session(%param);
		if (!defined $snmp_session) {
			printf "SNMP: %s\n", $snmp_error;
			exit $E_UNKNOWN;
		}
	}
	else {
		print "ERROR: You need perl module Net::SNMP to run $NAME in SNMP mode\n";
		exit $E_UNKNOWN;
	}
	return;
}

#
# Checking if SNMP works by probing for "chassisModelName", which all
# servers should have
#
sub snmp_check {
	my $chassisModelName = '1.3.6.1.4.1.674.10892.5.4.300.10.1.9.1';
	my $result = $snmp_session->get_request(-varbindlist => [ $chassisModelName ]);

	# Typically if remote host isn't responding
	if (!defined $result) {
		printf "SNMP CRITICAL: %s\n", $snmp_session->error;
		exit $E_CRITICAL;
	}

	# If OpenManage isn't installed or is not working
	if ($result->{$chassisModelName} =~ m{\A noSuch (Instance|Object) \z}xms) {
		print "ERROR: (SNMP) iSM is not installed in OS or is not working correctly\n";
		exit $E_UNKNOWN;
	}
	return;
}

#
# Detecting blade via SNMP
#
sub snmp_detect_blade {
	# In some setups, the IDs for the blade and interconnect
	# board are mixed up, so we need to check both.
	my $DellBaseBoardType1 = '1.3.6.1.4.1.674.10892.5.4.300.80.1.7.1.1';
	my $DellBaseBoardType2 = '1.3.6.1.4.1.674.10892.5.4.300.80.1.7.1.2';
	my $result1 = $snmp_session->get_request(-varbindlist => [ $DellBaseBoardType1 ]);
	my $result2 = $snmp_session->get_request(-varbindlist => [ $DellBaseBoardType2 ]);

	# Identify blade. Older models (4th and 5th gen models) and/or old
	# OMSA (4.x) don't have this OID. If we get "noSuchInstance" or
	# similar, we assume that this isn't a blade
	if (exists $result1->{$DellBaseBoardType1} && $result1->{$DellBaseBoardType1} eq '3') {
		$blade = 1;
		return;
	}
	if (exists $result2->{$DellBaseBoardType2} && $result2->{$DellBaseBoardType2} eq '3') {
		$blade = 1;
		return;
	}
	return;
}

#
# Read the blacklist option and return a hash containing the
# blacklisted components
#
sub set_blacklist {
	my $foo = shift;
	my @bl = ();

	if (scalar @{$foo} >= 0) {
		foreach my $black (@{$foo}) {
			my $tmp = q{};
			if (-f $black) {
				open my $BL, '<', $black
					or do {report('other', "Couldn't open blacklist file $black: $!", $E_UNKNOWN)
					and return {}};
				chomp($tmp = <$BL>);
				close $BL;
			}
			else {
				$tmp = $black;
			}
			push @bl, $tmp;
		}
	}

	return {} if $#bl < 0;

	# Parse blacklist string, put in hash
	foreach my $black (@bl) {
		my @comps = split m{/}xms, $black;
		foreach my $c (@comps) {
			next if $c !~ m/=/xms;
			my ($key, $val) = split /=/xms, $c;
			my @vals = split /,/xms, $val;
			push @{$blacklist{$key}}, @vals;
		}
	}

	return;
}

#
# Read the check option and adjust the hash %check, which is a rough
# list of components to be checked
#
sub adjust_checks {
	my @cl = ();

	# First, take the '--no-storage' option
	if ($opt{no_storage}) {
		$check{storage} = 0;
	}

	# Adjust checking based on the '--all' option
	if ($opt{all}) {
		# Check option usage
		if (defined $opt{only} and $opt{only} !~ m{\A critical|warning \z}xms) {
			print qq{ERROR: Wrong simultaneous usage of the "--all" and "--only" options\n};
			exit $E_UNKNOWN;
		}
		if (scalar @{$opt{check}} > 0) {
			print qq{ERROR: Wrong simultaneous usage of the "--all" and "--check" options\n};
			exit $E_UNKNOWN;
		}

		# set the check hash to check everything
		map {$_ = 1} values %check;

		return;
	}

	# Adjust checking based on the '--only' option
	if (defined $opt{only} and $opt{only} !~ m{\A critical|warning \z}xms) {
		# Check option usage
		if (scalar @{$opt{check}} > 0) {
			print qq{ERROR: Wrong simultaneous usage of the "--only" and "--check" options\n};
			exit $E_UNKNOWN;
		}
		if (!exists $check{$opt{only}} && $opt{only} ne 'chassis') {
			print qq{ERROR: "$opt{only}" is not a known keyword for the "--only" option\n};
			exit $E_UNKNOWN;
		}

		# reset the check hash
		map {$_ = 0} values %check;

		# adjust the check hash
		if ($opt{only} eq 'chassis') {
			map {$check{$_} = 1} qw(memory fans power temp cpu voltage sdcard
				batteries amperage intrusion);
		}
		else {
			$check{$opt{only}} = 1;
		}

		return;
	}

	# Adjust checking based on the '--check' option
	if (scalar @{$opt{check}} >= 0) {
		foreach my $check (@{$opt{check}}) {
			my $tmp = q{};
			if (-f $check) {
				open my $CL, '<', $check
					or do {report('other', "Couldn't open check file $check: $!", $E_UNKNOWN) and return};
				chomp($tmp = <$CL>);
				close $CL;
			}
			else {
				$tmp = $check;
			}
			push @cl, $tmp;
		}
	}

	return if $#cl < 0;

	# Parse checklist string, put in hash
	foreach my $check (@cl) {
		my @checks = split /,/xms, $check;
		foreach my $c (@checks) {
			next if $c !~ m/=/xms;
			my ($key, $val) = split /=/xms, $c;
			$check{$key} = $val;
		}
	}

	# Check if we should check global health status
	CHECK_KEY:
	foreach (keys %check) {
		next CHECK_KEY if $_ eq 'esmlog';   # not part of global status
		next CHECK_KEY if $_ eq 'alertlog'; # not part of global status

		if ($check{$_} == 0) {
			# found something with checking turned off
			$global = 0;
			last CHECK_KEY;
		}
	}

	return;
}

#
# Checks if a component is blacklisted. Returns 1 if the component is
# blacklisted, 0 otherwise. Takes two arguments:
#   arg1: component name
#   arg2: component id or index
#
sub blacklisted {
	my $name = shift; # component name
	my $id = shift;   # component id
	my $ret = 0;      # return value

	if (defined $blacklist{$name}) {
		foreach my $comp (@{$blacklist{$name}}) {
			if (defined $id and ($comp eq $id or uc($comp) eq 'ALL')) {
				$ret = 1;
			}
		}
	}

	return $ret;
}

# Converts the NexusID from SNMP to our version
sub convert_nexus {
	my $nexus = shift;
	$nexus =~ s{\A \\}{}xms;
	$nexus =~ s{\\}{:}gxms;
	return $nexus;
}

# Sets custom temperature thresholds based on user supplied options
sub custom_temperature_thresholds {
	my $type = shift; # type of threshold, either w (warning) or c (critical)
	my %thres = ();   # will contain the thresholds
	my @limits = ();  # holds the input

	my @opt = $type eq 'w' ? @{$opt{warning}} : @{$opt{critical}};

	if (scalar @opt >= 0) {
		foreach my $t (@opt) {
			my $tmp = q{};
			if (-f $t) {
				open my $F, '<', $t
					or do {report('other', "Couldn't open temperature threshold file $t: $!",
					$E_UNKNOWN) and return {}};
				$tmp = <$F>;
				close $F;
			}
			else {
				$tmp = $t;
			}
			push @limits, $tmp;
		}
	}

	# Parse checklist string, put in hash
	foreach my $th (@limits) {
		my @tmp = split m{,}xms, $th;
		foreach my $t (@tmp) {
			next if $t !~ m{=}xms;
			my ($key, $val) = split m{=}xms, $t;
			if ($val =~ m{/}xms) {
				my ($max, $min) = split m{/}xms, $val;
				$thres{$key}{max} = $max;
				$thres{$key}{min} = $min;
			}
			else {
				$thres{$key}{max} = $val;
			}
		}
	}

	return \%thres;
}


# Gets the output from SNMP result according to the OIDs checked
sub get_snmp_output {
	my ($result, $oidref) = @_;
	my @temp = ();
	my @output = ();

	foreach my $oid (keys %{$result}) {
		my $short = $oid;
		$short =~ s{\s}{}gxms;                   # remove whitespace
		$short =~ s{\A (.+) \. (\d+) \z}{$1}xms; # remove last number
		my $id = $2;
		if (exists $oidref->{$short}) {
			$temp[$id]{$oidref->{$short}} = $result->{$oid};
		}
	}

	# Remove any empty indexes
	foreach my $out (@temp) {
		if (defined $out) {
			push @output, $out;
		}
	}

	return \@output;
}


# Map the controller or other item in-place
sub map_item {
	my ($key, $val, $list) = @_;

	foreach my $lst (@{$list}) {
		if (!exists $lst->{$key}) {
			$lst->{$key} = $val;
		}
	}
	return;
}

# Return the URL for official Dell documentation for a specific
# PowerEdge server
sub documentation_url {
	my $model = shift;
	my $rev = shift;

	# Special case: R210 II
	if ($model eq 'R210' and $rev eq 'II') {
		$model = 'r210-2';
	}

	# create model name used in URLs, e.g. "poweredge-r710"
	$model = lc($model);
	$model =~ s{\s}{-}xms;

	if (exists $country{$opt{htmlinfo}}) {
		return sprintf 'http://www.dell.com/support/troubleshooting/%s/%s/19/Product/%s#ui-tabs-4',
			$country{$opt{htmlinfo}}->{c}, $country{$opt{htmlinfo}}->{l}, $model;
	}
	else {
		return sprintf 'http://www.dell.com/support/troubleshooting/us/en/19/Product/%s#ui-tabs-4',
			$model;
	}
	return;
}

# Return the URL for warranty information for a server with a given
# serial number (servicetag)
sub warranty_url {
	my $tag = shift;
	my $url_start = 'http://www.dell.com/support/troubleshooting';
	my $url_end = 'Index?t=warranty&servicetag';

	if (exists $country{$opt{htmlinfo}}) {
		return sprintf '%s/%s/%s/nodhs1/%s=%s',
			$url_start, $country{$opt{htmlinfo}}->{c},
			$country{$opt{htmlinfo}}->{l}, $url_end, $tag;
	}
	else {
		return sprintf '%s/%s=%s', $url_start, $url_end, $tag;
	}
}


# This helper function returns the corresponding value of a hash key,
# but takes into account that the key may not exist
sub get_hashval {
	my $key = shift || return;
	my $hash = shift;
	return defined $hash->{$key} ? $hash->{$key} : "Undefined value $key";
}

# Find component status from hash
sub get_snmp_status {
	my $key = shift || return 'Unknown';
	return exists $snmp_status{$key} ? $snmp_status{$key} : 'Unknown';
}

# Find component status from hash
sub get_snmp_probestatus {
	my $key = shift || return 'Unknown';
	return exists $snmp_probestatus{$key} ? $snmp_probestatus{$key} : 'Unknown';
}

# Check that a hash entry is defined and not an empty string. Return a
# chosen string (parameter) if these conditions are not met
sub get_nonempty_string {
	my $key = shift;  # key to check
	my $hash = shift; # hash where the key belongs
	my $alt = shift;  # alternate return value
	if (defined $hash->{$key} and $hash->{$key} ne q{}) {
		return $hash->{$key};
	}
	return $alt;
}

# Converts from Celsius to something else
sub temp_from_celsius {
	my $x = shift;
	my $to = shift;

	if ($to eq 'F') {
		return sprintf '%.1f', ($x * 9 / 5 + 32);
	}
	elsif ($to eq 'K') {
		return sprintf '%.1f', ($x + 273.15);
	}
	elsif ($to eq 'R') {
		return sprintf '%.1f', ($x * 9 / 5 + 32 + 459.67);
	}
	return $x;
}


#---------------------------------------------------------------------
# Check functions
#---------------------------------------------------------------------

#-----------------------------------------
# Check global health status
#-----------------------------------------
sub check_global {
	my $health = $E_OK;

	if ($snmp) {
		#
		# Checks global status, i.e. both storage and chassis
		#
		my $systemStateGlobalSystemStatus = '1.3.6.1.4.1.674.10892.5.4.200.10.1.2.1';
		my $result = $snmp_session->get_request(-varbindlist => [ $systemStateGlobalSystemStatus ]);
		if (!defined $result) {
			printf "SNMP ERROR [global]: %s\n", $snmp_error;
			exit $E_UNKNOWN;
		}
		$health = $status2nagios{get_snmp_status($result->{$systemStateGlobalSystemStatus})};
	}

	# Return the status
	return $health;
}


#-----------------------------------------
# STORAGE: Check controllers
#-----------------------------------------
sub check_controllers {
	my $nexus = undef;
	my $name = undef;
	my $state = undef;
	my $status = undef;
	#    my $minfw    = undef;
	#    my $mindr    = undef;
	my $firmware = undef;
	my $driver = undef;
	#    my $minstdr  = undef;  # Minimum required Storport driver version
	#    my $stdr     = undef;  # Storport driver version
	my @output = ();

	if ($snmp) {
		my %ctrl_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.1'  => 'controllerNumber',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.2'  => 'controllerName',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.8'  => 'controllerFWVersion',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.37' => 'controllerRollUpStatus',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.38' => 'controllerComponentStatus',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.41' => 'controllerDriverVersion',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.44' => 'controllerMinFWVersion',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.45' => 'controllerMinDriverVersion',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.55' => 'controllerStorportDriverVersion',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.56' => 'controllerMinRequiredStorportVer',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.78' => 'controllerFQDD', # was controllerNexusID under OID '1.3.6.1.4.1.674.10892.5.5.1.20.130.1.1.39'
		);

		# We use get_table() here for the odd case where a server has
		# two or more controllers, and where some OIDs are missing on
		# one of the controllers.
		my $controllerTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.1';
		my $result = $snmp_session->get_table(-baseoid => $controllerTable);

		if (!defined $result) {
			report('storage', 'Storage Error! No controllers found', $E_UNKNOWN);
			return;
		}

		@output = @{get_snmp_output($result, \%ctrl_oid)};
	}

	## OK - updated for iSM
	my %ctrl_state
		= (
		0 => 'Unknown',
		1 => 'Other',
		2 => 'Unknown',
		3 => 'OK',
		4 => 'Non-critical',
		5 => 'Critical',
		6 => 'Non-recoverable',
	);

	CTRL:
	foreach my $out (@output) {
		if ($snmp) {
			$name = $out->{controllerName} || 'Unknown controller';
			$state = get_hashval($out->{controllerRollUpStatus}, \%ctrl_state) || 'Unknown state';
			$status = get_snmp_status($out->{controllerComponentStatus});
			#	    $minfw    = $out->{controllerMinFWVersion} || undef;
			#	    $mindr    = $out->{controllerMinDriverVersion} || undef;
			$firmware = $out->{controllerFWVersion} || 'N/A';
			$driver = $out->{controllerDriverVersion} || 'N/A';
			#	    $minstdr  = $out->{'controllerMinRequiredStorportVer'} || undef;
			#	    $stdr     = $out->{controllerStorportDriverVersion} || undef;
			$nexus = convert_nexus(($out->{controllerFQDD} || 9999));
		}

		$name =~ s{\s+\z}{}xms; # remove trailing whitespace
		push @controllers, $nexus;

		# Collecting some storage info
		$sysinfo{'controller'}{$nexus}{'id'} = $nexus;
		$sysinfo{'controller'}{$nexus}{'name'} = $name;
		$sysinfo{'controller'}{$nexus}{'driver'} = $driver;
		$sysinfo{'controller'}{$nexus}{'firmware'} = $firmware;
		#	$sysinfo{'controller'}{$nexus}{'storport'} = $stdr;

		# Store controller info for future use (SNMP)
		if ($snmp) {
			$snmp_controller{$out->{controllerNumber}} = $nexus;
		}

		next CTRL if blacklisted('ctrl', $nexus);

		# Ok
		if ($status eq 'Ok' or ($status eq 'Non-Critical')) {
			my $msg = sprintf 'Controller %s [%s] is %s',
				$nexus, $name, $state;
			report('storage', $msg, $E_OK, $nexus);
		}
		# Default
		else {
			my $msg = sprintf 'Controller %s [%s] is %s',
				$nexus, $name, $state;
			report('storage', $msg, $status2nagios{$status}, $nexus);
		}
	}
	return;
}


#-----------------------------------------
# STORAGE: Check physical drives
#-----------------------------------------
sub check_physical_disks {
	return if $#controllers == -1;

	my $nexus = undef;
	my $name = undef;
	my $state = undef;
	my $status = undef;
	my $fpred = undef;
	my $progr = undef;
	my $ctrl = undef;
	my $vendor = undef;   # disk vendor
	my $product = undef;  # product ID
	my $capacity = undef; # disk length (size) in bytes
	my $media = undef;    # media type (e.g. HDD, SSD)
	my $bus = undef;      # bus protocol (e.g. SAS, SATA)
	my $spare = undef;    # spare state (e.g. global hotspare)
	#   my $cert     = undef;  # if drive is certified or not
	my @output = ();

	if ($snmp) {
		my %pdisk_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.2'  => 'physicalDiskName',         #was arrayDiskName
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.3'  => 'physicalDiskManufacturer', # was arrayDiskVendor
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.4'  => 'physicalDiskState',        # was arrayDiskState
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.6'  => 'physicalDiskProductID',    #was arrayDiskProductID
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.9'  => 'arrayDiskEnclosureID',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.10' => 'arrayDiskChannel',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.11' => 'physicalDiskCapacityInMB', # was arrayDiskLengthInMB
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.15' => 'arrayDiskTargetID',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.21' => 'physicalDiskBusType',         # was arrayDiskBusType
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.22' => 'physicalDiskSpareState',      # was arrayDiskSpareState
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.24' => 'physicalDiskComponentStatus', # was arrayDiskComponentStatus
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.26' => 'arrayDiskNexusID', #replaced by physicalDiskFQDD
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.31' => 'physicalDiskSmartAlertIndication', # was arrayDiskSmartAlertIndication
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.35' => 'physicalDiskMediaType',            # was arrayDiskMediaType
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.36' => 'arrayDiskDellCertified',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.4.1.54' => 'physicalDiskFQDD', # replaces arrayDiskNexusID
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.5.1.7'  => 'arrayDiskEnclosureConnectionControllerNumber',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.6.1.7'  => 'arrayDiskChannelConnectionControllerNumber',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $arrayDiskTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.4';
			# my $arrayDiskEnclosureConnectionControllerNumber = '1.3.6.1.4.1.674.10892.5.5.1.20.130.5.1.7';
			# my $arrayDiskChannelConnectionControllerNumber = '1.3.6.1.4.1.674.10892.5.5.1.20.130.6.1.7';

			$result = $snmp_session->get_table(-baseoid => $arrayDiskTable);
			#my $ext1 = $snmp_session->get_table(-baseoid => $arrayDiskEnclosureConnectionControllerNumber);
			#my $ext2 = $snmp_session->get_table(-baseoid => $arrayDiskChannelConnectionControllerNumber);

			#	    if (defined $result) {
			#		defined $ext1 && map { $$result{$_} = $$ext1{$_} } keys %{ $ext1 };
			#		defined $ext2 && map { $$result{$_} = $$ext2{$_} } keys %{ $ext2 };
			#	    }
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %pdisk_oid ]);
		}

		if (!defined $result) {
			printf "SNMP ERROR [storage / pdisk]: %s.\n", $snmp_session->error;
			$snmp_session->close;
			exit $E_UNKNOWN;
		}

		@output = @{get_snmp_output($result, \%pdisk_oid)};
	}

	## OK - updated for iSM
	my %spare_state
		= (
		1 => 'Not a spare',
		2 => 'Dedicated HS',
		3 => 'Global HS',
	);

	## OK - updated for iSM
	my %media_type
		= (
		1 => 'unknown',
		2 => 'HDD',
		3 => 'SSD',
	);

	## OK - updated for iSM
	my %bus_type
		= (
		1 => 'Unknown',
		2 => 'SCSI',
		3 => 'SAS',
		4 => 'SATA',
		5 => 'FC',
		6 => 'PCIe',
		7 => 'NVMe',
	);

	## OK - updated for iSM
	my %pdisk_state
		= (
		1  => 'Unknown',
		2  => 'Ready',
		3  => 'Online',
		4  => 'Foreign',
		5  => 'Offline',
		6  => 'Blocked',
		7  => 'Failed',
		8  => 'non-RAID',
		9  => 'Removed',
		10 => 'Read-only',
	);

	# Check physical disks on each of the controllers
	PDISK:
	foreach my $out (@output) {
		if ($snmp) {
			$name = $out->{physicalDiskName} || 'Unknown disk';
			$state = get_hashval($out->{physicalDiskState}, \%pdisk_state) || 'Unknown state';
			$status = get_snmp_status($out->{physicalDiskComponentStatus});
			$fpred = defined $out->{physicalDiskSmartAlertIndication}
				&& $out->{physicalDiskSmartAlertIndication} == 2 ? 1 : 0;
			$progr = q{};
			$nexus = convert_nexus(($out->{physicalDiskFQDD} || 9999));
			$vendor = $out->{physicalDiskManufacturer} || 'Unknown manufacturer';
			$product = $out->{physicalDiskProductID} || 'Unknown product ID';
			$spare = get_hashval($out->{physicalDiskSpareState}, \%spare_state) || q{};
			$bus = get_hashval($out->{physicalDiskBusType}, \%bus_type);
			$media = get_hashval($out->{physicalDiskMediaType}, \%media_type);
			#$cert     = defined $out->{arrayDiskDellCertified} ? $out->{arrayDiskDellCertified} : 1;
			$capacity = exists $out->{physicalDiskCapacityInMB}
				? $out->{physicalDiskCapacityInMB} * 1024 ** 2 : -1;

			#	    # try to find the controller where the disk belongs
			#	    if (exists $out->{arrayDiskEnclosureConnectionControllerNumber}) {
			#		# for disks that are attached to an enclosure
			#		$ctrl = $snmp_controller{$out->{arrayDiskEnclosureConnectionControllerNumber}};
			#	    }
			#	    elsif (exists $out->{arrayDiskChannelConnectionControllerNumber}) {
			#		# for disks that are not attached to an enclosure
			#		$ctrl = $snmp_controller{$out->{arrayDiskChannelConnectionControllerNumber}};
			#	    }
			#	    else {
			# last resort... use the nexus id (old/broken hardware)
			$ctrl = $nexus;
			$ctrl =~ s{\A (\d+) : .* \z}{$1}xms;
			#	    }

			#	    # workaround for OMSA 7.1.0 bug
			#	    if ($snmp && $sysinfo{om} eq '7.1.0') {
			#		if    ($cert == 1) { $cert = 0; }
			#		elsif ($cert == 0) { $cert = 1; }
			#	    }
		}

		$count{pdisk}++;
		next PDISK if blacklisted('pdisk', $nexus);

		$vendor =~ s{\s+\z}{}xms;  # remove trailing whitespace
		$product =~ s{\s+\z}{}xms; # remove trailing whitespace

		# If the disk is bad, the vendor field may be empty
		if ($vendor eq q{}) {$vendor = 'Unknown Vendor';}

		# Hot spare stuff
		if ($spare eq 'Global') {$spare = 'Global HS';}
		elsif ($spare eq 'Dedicated') {$spare = 'Dedicated HS';}
		elsif ($spare !~ m{\A Global|Dedicated}xms) {$spare = undef;}

		# Calculate human readable capacity
		if ($capacity == -1) {
			# capacity is unknown
			$capacity = 'Unknown Size';
		}
		else {
			$capacity = ceil($capacity / 1000 ** 3) >= 1000
				? sprintf '%.1fTB', ($capacity / 1000 ** 4)
				: sprintf '%.0fGB', ($capacity / 1000 ** 3);
		}

		# Capitalize only the first letter of the vendor name
		$vendor = (substr $vendor, 0, 1) . lc(substr $vendor, 1, length $vendor);

		# Remove unnecessary trademark rubbish from vendor name
		$vendor =~ s{\(tm\)\z}{}xms;

		# bus and media aren't always defined
		my $busmedia = q{};
		if (defined $bus && defined $media) {$busmedia = "$bus-$media ";}
		elsif (defined $bus && !defined $media) {$busmedia = "$bus ";}
		elsif (!defined $bus && defined $media) {$busmedia = "$media ";}

		# Variables to collect statuses and states
		my @states = ($state);
		my $stack = $status2nagios{$status};

		# Special case: Failure predicted
		if ($fpred) {
			push @states, 'Failure Predicted';
			++$stack if $stack == 0;
		}
		#	# Special case: Uncertified disk
		#	if (!$cert) {
		#	    # Functional non Dell disks get a Non-Critical status
		#	    if (($state eq 'Online' or $state eq 'Ready' or $state eq 'Non-RAID')
		#		and $status eq 'Non-Critical' and not $fpred
		#		and blacklisted('pdisk_cert', $nexus)) {
		#		--$stack;
		#	    }
		#	    else {
		#		push @states, 'Not Certified';
		#	    }
		#	}
		# Special case: Foreign disk
		if ($state eq 'Foreign' and blacklisted('pdisk_foreign', $nexus)) {
			--$stack;
		}

		# Set failed disk as critical (override OMSA)
		if ($state eq 'Failed') {
			$stack = 2;
		}

		# Create combined status and state
		my $combo_state = join ', ', @states;
		my $combo_status = undef;
		if ($stack >= 2) {$combo_status = $E_CRITICAL;}
		elsif ($stack == 1) {$combo_status = $E_WARNING;}
		elsif ($stack <= 0) {$combo_status = $E_OK;}

		# Special case: Rebuilding / Replacing
		if ($state =~ m{\A Rebuilding|Replacing \z}xms) {
			my $msg = sprintf '%s [%s %s, %s] on ctrl %d is %s%s',
				$name, $vendor, $product, $capacity, $ctrl, $state, $progr;
			report('storage', $msg, $E_WARNING, $nexus);
		}
		# Default
		elsif ($combo_status != $E_OK) {
			my $msg = sprintf '%s [%s %s, %s] on ctrl %d is %s',
				$name, $vendor, $product, $capacity, $ctrl, $combo_state;
			report('storage', $msg, $combo_status, $nexus);
		}
		# Ok
		else {
			my $msg = sprintf '%s [%s%s] on ctrl %s is %s',
				$name, $busmedia, $capacity, $ctrl, $combo_state;
			if (defined $spare) {$msg .= " ($spare)";}
			report('storage', $msg, $E_OK, $nexus);
		}
	}
	return;
}


#-----------------------------------------
# STORAGE: Check logical drives
#-----------------------------------------
sub check_virtual_disks {
	return if $#controllers == -1;

	my $name = undef;
	my $nexus = undef;
	my $dev = undef;
	my $state = undef;
	my $op_state = undef;
	my $status = undef;
	my $layout = undef;
	my $size = undef;
	my $progr = undef;
	my $ctrl = undef;
	my @output = ();

	if ($snmp) {
		my %vdisk_oid
			= (
			#'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.3'  => 'virtualDiskDeviceName', # replaced by virtualDiskName
			'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.2'  => 'virtualDiskName', # was virtualDiskDeviceName
			'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.4'  => 'virtualDiskState',
			'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.6'  => 'virtualDiskSizeInMB', # was virtualDiskLengthInMB
			'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.13' => 'virtualDiskLayout',
			'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.20' => 'virtualDiskComponentStatus',
			'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.30' => 'virtualDiskOperationalState',
			# '1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.21' => 'virtualDiskNexusID', # replaced by virtualDiskFQDD
			'1.3.6.1.4.1.674.10892.5.5.1.20.140.1.1.35' => 'virtualDiskFQDD', # was virtualDiskNexusID
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $virtualDiskTable = '1.3.6.1.4.1.674.10892.5.5.1.20.140.1';
			$result = $snmp_session->get_table(-baseoid => $virtualDiskTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %vdisk_oid ]);
		}

		# No logical drives is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%vdisk_oid)};
	}

	## OK - updated for iSM (new!)
	my %vdisk_op_state
		= (
		0 => 'Unknown',
		1 => 'N/A',
		2 => 'Reconstructing',
		3 => 'Resynching',
		4 => 'Initialization',
		5 => 'Failed',
	);

	## OK - updated for iSM
	my %vdisk_state
		= (
		1 => 'Unknown',
		2 => 'Online',
		3 => 'Failed',
		4 => 'Degraded',
	);

	## OK - updated for iSM
	my %vdisk_layout
		= (
		1  => 'Other',
		2  => 'RAID-0',
		3  => 'RAID-1',
		4  => 'RAID-5',
		5  => 'RAID-6',
		6  => 'RAID-10',
		7  => 'RAID-50',
		8  => 'RAID-60',
		9  => 'Concatenated RAID-1',
		10 => 'Concatenated RAID-5',
	);

	# Check virtual disks on each of the controllers
	VDISK:
	foreach my $out (@output) {
		if ($snmp) {
			$dev = $out->{virtualDiskName} || 'Unknown device';
			$state = get_hashval($out->{virtualDiskState}, \%vdisk_state) || 'Unknown state';
			$op_state = get_hashval($out->{virtualDiskOperationalState}, \%vdisk_op_state) || 'Unknown operation in progress';
			$layout = get_hashval($out->{virtualDiskLayout}, \%vdisk_layout) || 'Unknown layout';
			$status = get_snmp_status($out->{virtualDiskComponentStatus});
			$size = sprintf '%.2f GB', ($out->{virtualDiskSizeInMB} || 0) / 1024;
			$progr = q{}; # not available via SNMP
			$nexus = convert_nexus(($out->{virtualDiskFQDD} || 9999));
		}

		$count{vdisk}++;
		next VDISK if blacklisted('vdisk', $nexus);

		# The device name is undefined sometimes
		$dev = q{} if !defined $dev;

		# Special case: Regenerating
		if ($state eq 'Regenerating') {
			my $msg = sprintf q{Logical Drive '%s' [%s, %s] is %s (%s) %s},
				$dev, $layout, $size, $state, $op_state, $progr;
			my $lvl = $opt{vdisk_critical} ? $E_CRITICAL : $E_WARNING;
			report('storage', $msg, $lvl, $nexus);
		}
		# Default
		else {
			my $msg = sprintf q{Logical Drive '%s' [%s, %s] is %s (%s)},
				$dev, $layout, $size, $state, $op_state;
			my $lvl = $status2nagios{$status};
			if ($opt{vdisk_critical} && $lvl != $E_OK) {
				$lvl = $E_CRITICAL;
			}
			report('storage', $msg, $lvl, $nexus);
		}
	}
	return;
}


#-----------------------------------------
# STORAGE: Check cache batteries
#-----------------------------------------
sub check_cache_battery {
	return if $#controllers == -1;

	my $id = undef;
	my $nexus = undef;
	my $state = undef;
	my $status = undef;
	my $ctrl = undef;
	my $learn = undef; # learn state
	my $pred = undef;  # battery's ability to be charged
	my @output = ();

	if ($snmp) {
		my %bat_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.15.1.4'  => 'batteryState',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.15.1.6'  => 'batteryComponentStatus',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.15.1.9'  => 'batteryNexusID', # replaced by batteryFQDD
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.15.1.10' => 'batteryPredictedCapacity',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.15.1.12' => 'batteryLearnState',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.16.1.5'  => 'batteryConnectionControllerNumber',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.15.1.20' => 'batteryFQDD', # was batteryNexusID
		);
		my $result = undef;
		$result = $snmp_session->get_entries(-columns => [ keys %bat_oid ]);

		# No cache battery is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%bat_oid)};
	}

	## OK - updated for iSM
	my %bat_state
		= (
		1 => 'Unknown',
		2 => 'Ready',
		3 => 'Failed',
		4 => 'Degraded',
		5 => 'Missing',
		6 => 'Charging',
		7 => 'Below Threshold',
	);

	# Check battery on each of the controllers
	BATTERY:
	foreach my $out (@output) {
		if ($snmp) {
			$status = get_snmp_status($out->{batteryComponentStatus});
			$state = get_hashval($out->{batteryState}, \%bat_state) || 'Unknown state';
			#$learn  = get_hashval($out->{batteryLearnState}, \%bat_learn_state) || 'Unknown learn state';
			#$pred   = get_hashval($out->{batteryPredictedCapacity}, \%bat_pred_cap) || 'Unknown predicted capacity status';
			#$ctrl   = $snmp_controller{$out->{batteryConnectionControllerNumber}};
			$nexus = convert_nexus(($out->{batteryFQDD} || 9999));
			$id = $nexus;
			$id =~ s{\A \d+:(\d+) \z}{$1}xms;
		}

		next BATTERY if blacklisted('bat', $nexus);

		## TODO fix logic for battery status - it is not working correctly after moving to iSM
		# Special case: Charging
		if ($state eq 'Charging') {
			if ($pred eq 'Failed') {
				my $msg = sprintf 'Cache Battery %d is %s (%s) [replace battery]',
					$id, $state, $pred;
				report('storage', $msg, $E_CRITICAL, $nexus);
			}
			else {
				next BATTERY if blacklisted('bat_charge', $nexus);
				my $msg = sprintf 'Cache Battery %d is %s (%s) [probably harmless]',
					$id, $state, $pred;
				report('storage', $msg, $E_WARNING, $nexus);
			}
		}
		# Special case: Learning (battery learns its capacity)
		elsif ($state eq 'Learning') {
			if ($learn eq 'Failed') {
				my $msg = sprintf 'Cache Battery %d is %s (%s)',
					$id, $state, $learn;
				report('storage', $msg, $E_CRITICAL, $nexus);
			}
			else {
				next BATTERY if blacklisted('bat_charge', $nexus);
				my $msg = sprintf 'Cache Battery %d is %s (%s) [probably harmless]',
					$id, $state, $learn;
				report('storage', $msg, $E_WARNING, $nexus);
			}
		}
		# Special case: Power Low (first part of recharge cycle)
		elsif ($state eq 'Power Low') {
			next BATTERY if blacklisted('bat_charge', $nexus);
			my $msg = sprintf 'Cache Battery %d in is %s [probably harmless]',
				$id, $state;
			report('storage', $msg, $E_WARNING, $nexus);
		}
		# Special case: Degraded and Non-Critical (usually part of recharge cycle)
		elsif ($state eq 'Degraded' && $status eq 'Non-Critical') {
			next BATTERY if blacklisted('bat_charge', $nexus);
			my $msg = sprintf 'Cache Battery %d is %s (%s) [probably harmless]',
				$id, $state, $status;
			report('storage', $msg, $E_WARNING, $nexus);
		}
		# Special case: Ready and Non-Critical and "Unknown" predicted status
		elsif ($state eq 'Ready' && $status eq 'Non-Critical' && $pred eq 'Unknown') {
			next BATTERY if blacklisted('bat_charge', $nexus);
			my $msg = sprintf 'Cache Battery %d predicted capacity is %s [probably harmless]',
				$id, $pred;
			report('storage', $msg, $E_WARNING, $nexus);
		}
		# Default
		else {
			my $msg = sprintf 'Cache Battery %s is %s',
				$id, $state;
			report('storage', $msg, $status2nagios{$status}, $nexus);
		}
	}
	return;
}

#-----------------------------------------
# STORAGE: Check enclosures
#-----------------------------------------
sub check_enclosures {
	my $id = undef;
	my $nexus = undef;
	my $name = undef;
	my $state = undef;
	my $rollup = undef;
	my $status = undef;
	my $firmware = undef;
	my $ctrl = undef;
	my $occupied_slots = undef; # number of occupied slots
	my $total_slots = undef;    # number of total slots
	my @output = ();

	if ($snmp) {
		my %encl_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.1'  => 'enclosureNumber',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.2'  => 'enclosureName',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.4'  => 'enclosureState',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.24' => 'enclosureComponentStatus',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.25' => 'enclosureNexusID', # replaced by enclosureFQDD
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.26' => 'enclosureFirmwareVersion',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.31' => 'enclosureOccupiedSlotCount',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.32' => 'enclosureTotalSlots',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.3.1.47' => 'enclosureFQDD', # was enclosureNexusID
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $enclosureTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.3';
			$result = $snmp_session->get_table(-baseoid => $enclosureTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %encl_oid ]);
		}

		# No enclosures is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%encl_oid)};
	}

	## OK - updated for iSM
	my %encl_state
		= (
		1 => 'Unknown',
		2 => 'Ready',
		3 => 'Failed',
		4 => 'Missing',
		5 => 'Degraded',
	);

	ENCLOSURE:
	foreach my $out (@output) {
		if ($snmp) {
			$id = ($out->{enclosureNumber} || 10000) - 1;
			$name = $out->{enclosureName} || 'Unknown enclosure';
			$state = get_hashval($out->{enclosureState}, \%encl_state) || 'Unknown state';
			$status = get_snmp_status($out->{enclosureComponentStatus});
			$firmware = $out->{enclosureFirmwareVersion} || 'N/A';
			$nexus = convert_nexus(($out->{enclosureFQDD} || 9999));
			$ctrl = $nexus;
			$ctrl =~ s{\A (\d+):.* \z}{$1}xms;
			# for the next two, a value of 9999 means feature not available
			$occupied_slots = defined $out->{enclosureOccupiedSlotCount}
				&& $out->{enclosureOccupiedSlotCount} != 9999
				? $out->{enclosureOccupiedSlotCount} : undef;
			$total_slots = defined $out->{enclosureTotalSlots}
				&& $out->{enclosureTotalSlots} != 9999
				? $out->{enclosureTotalSlots} : undef;
		}

		# store enclosure data for future use
		if ($snmp) {
			$snmp_enclosure{$out->{enclosureNumber}}{id} = $id;
			$snmp_enclosure{$out->{enclosureNumber}}{name} = $name;
			$snmp_enclosure{$out->{enclosureNumber}}{nexus} = $nexus;
		}
		else {
			push @enclosures, { 'id' => $id,
				'ctrl'               => $out->{ctrl},
				'name'               => $name };
		}

		# Collecting some storage info
		$sysinfo{'enclosure'}{$nexus}{'id'} = $nexus;
		$sysinfo{'enclosure'}{$nexus}{'name'} = $name;
		$sysinfo{'enclosure'}{$nexus}{'firmware'} = $firmware;

		next ENCLOSURE if blacklisted('encl', $nexus);

		my $msg = q{};
		if (defined $occupied_slots && defined $total_slots) {
			$msg = sprintf 'Enclosure %s [%s, %d/%d slots occupied] on ctrl %s is %s',
				$nexus, $name, $occupied_slots, $total_slots, $ctrl, $state;
		}
		else {
			$msg = sprintf 'Enclosure %s [%s] on controller %d is %s',
				$nexus, $name, $ctrl, $state;
		}
		report('storage', $msg, $status2nagios{$status}, $nexus);
	}
	return;
}


#-----------------------------------------
# STORAGE: Check enclosure fans
#-----------------------------------------
sub check_enclosure_fans {
	return if $#controllers == -1;

	my $nexus = undef;
	my $name = undef;
	my $state = undef;
	my $status = undef;
	my $comp_stat = undef;
	my $speed = undef;
	my $encl_id = undef;
	my $encl_name = undef;
	my @output = ();

	if ($snmp) {
		my %fan_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.7.1.2'  => 'enclosureFanName',            # was fanName
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.7.1.4'  => 'enclosureFanState',           # was fanState
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.7.1.11' => 'enclosureFanProbeCurrValue',  # was fanProbeCurrValue
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.7.1.15' => 'enclosureFanComponentStatus', # was fanComponentStatus
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.7.1.16' => 'fanNexusID', # replaced by enclosureFanFQDD
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.8.1.4'  => 'fanConnectionEnclosureName',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.8.1.5'  => 'fanConnectionEnclosureNumber',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.7.1.20' => 'enclosureFanFQDD', # was fanNexusID
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $fanTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.7';
			my $fanConnectionTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.8';

			$result = $snmp_session->get_table(-baseoid => $fanTable);
			my $ext = $snmp_session->get_table(-baseoid => $fanConnectionTable);

			if (defined $result) {
				defined $ext && map {$$result{$_} = $$ext{$_}} keys %{$ext};
			}
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %fan_oid ]);
		}

		# No enclosure fans is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%fan_oid)};
	}

	## OK - updated for iSM
	my %fan_state
		= (
		1 => 'Unknown',
		2 => 'Ready',
		3 => 'Failed',
		4 => 'Missing',
		5 => 'Degraded',
	);

	# Check fans on each of the enclosures
	FAN:
	foreach my $out (@output) {
		if ($snmp) {
			$name = $out->{enclosureFanName} || 'Unknown fan';
			$state = get_hashval($out->{enclosureFanState}, \%fan_state) || 'Unknown state';
			$status = get_snmp_status($out->{enclosureFanComponentStatus});
			$speed = $out->{enclosureFanProbeCurrValue} || 'N/A';
			#$encl_name = $out->{fanConnectionEnclosureName} || 'Unknown enclosure';
			#$encl_id   = $snmp_enclosure{$out->{fanConnectionEnclosureNumber}}{nexus};
			$nexus = convert_nexus(($out->{enclosureFanFQDD} || 9999));
		}

		next FAN if blacklisted('encl_fan', $nexus);

		# Default
		if ($status ne 'Ok') {
			my $msg = sprintf 'Fan %s is %s',
				$name, $state;
			report('storage', $msg, $status2nagios{$status}, $nexus);
		}
		# Ok
		else {
			my $msg = sprintf 'Fan %s is %s (%s - speed %s)',
				$name, $status, $state, $speed;
			report('storage', $msg, $E_OK, $nexus);
		}
	}
	return;
}


#-----------------------------------------
# STORAGE: Check enclosure power supplies
#-----------------------------------------
sub check_enclosure_pwr {
	return if $#controllers == -1;

	my $nexus = undef;
	my $name = undef;
	my $state = undef;
	my $status = undef;
	my $encl_id = undef;
	my $encl_name = undef;
	my @output = ();

	if ($snmp) {
		my %ps_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.9.1.2'  => 'enclosurePowerSupplyName',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.9.1.4'  => 'enclosurePowerSupplyState',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.9.1.9'  => 'enclosurePpowerSupplyComponentStatus',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.9.1.10' => 'powerSupplyNexusID', # replaced by enclosurePowerSupplyFQDD
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.9.1.15' => 'enclosurePowerSupplyFQDD', # was powerSupplyNexusID
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.10.1.4' => 'powerSupplyConnectionEnclosureName',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.10.1.5' => 'powerSupplyConnectionEnclosureNumber',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $powerSupplyTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.9';
			#my $powerSupplyConnectionTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.10';

			$result = $snmp_session->get_table(-baseoid => $powerSupplyTable);
			#my $ext = $snmp_session->get_table(-baseoid => $powerSupplyConnectionTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %ps_oid ]);
		}

		# No enclosure power supplies is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%ps_oid)};
	}

	## OK - updated for iSM
	my %ps_state
		= (
		1 => 'Unknown',
		2 => 'Ready',
		3 => 'Failed',
		4 => 'Missing',
		5 => 'Degraded',
	);

	# Check power supplies on each of the enclosures
	PS:
	foreach my $out (@output) {
		if ($snmp) {
			$name = $out->{enclosurePowerSupplyName} || 'Unknown PSU';
			$state = get_hashval($out->{enclosurePowerSupplyState}, \%ps_state) || 'Unknown state';
			$status = get_snmp_status($out->{enclosurePpowerSupplyComponentStatus});
			#	    $encl_id   = $snmp_enclosure{$out->{powerSupplyConnectionEnclosureNumber}}{nexus};
			#	    $encl_name = $out->{powerSupplyConnectionEnclosureName} || 'Unknown enclosure';
			$nexus = convert_nexus(($out->{enclosurePowerSupplyFQDD} || 9999));
		}

		next PS if blacklisted('encl_ps', $nexus);

		# Default
		my $msg = sprintf '%s is %s (%s)',
			$name, $state, $status;
		report('storage', $msg, $status2nagios{$status}, $nexus);
	}
	return;
}


#-----------------------------------------
# STORAGE: Check enclosure temperatures
#-----------------------------------------
sub check_enclosure_temp {
	return if $#controllers == -1;

	my $nexus = undef;
	my $name = undef;
	my $state = undef;
	my $status = undef;
	my $reading = undef;
	my $unit = undef;
	my $max_warn = undef;
	my $max_crit = undef;
	my $min_warn = undef;
	my $min_crit = undef;
	my $encl_id = undef;
	my $encl_name = undef;
	my @output = ();

	if ($snmp) {
		my %temp_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.2'  => 'enclosureTemperatureProbeName',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.4'  => 'enclosureTemperatureProbeState',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.6'  => 'temperatureProbeUnit',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.7'  => 'enclosureTemperatureProbeMinWarning',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.8'  => 'enclosureTemperatureProbeMinCritical',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.9'  => 'enclosureTemperatureProbeMaxWarning',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.10' => 'enclosureTemperatureProbeMaxCritical',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.11' => 'enclosureTemperatureProbeCurValue',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.13' => 'enclosureTemperatureProbeComponentStatus',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.14' => 'temperatureProbeNexusID', # replaced by enclosureTemperatureProbeFQDD
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.11.1.15' => 'enclosureTemperatureProbeFQDD', # was temperatureProbeNexusID
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.12.1.4'  => 'temperatureConnectionEnclosureName',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.12.1.5'  => 'temperatureConnectionEnclosureNumber',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $temperatureProbeTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.11';
			#my $temperatureConnectionTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.12';

			$result = $snmp_session->get_table(-baseoid => $temperatureProbeTable);
			#my $ext = $snmp_session->get_table(-baseoid => $temperatureConnectionTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %temp_oid ]);
		}

		# No enclosure temperature probes is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%temp_oid)};
	}

	## OK - updated for iSM
	my %temp_state
		= (
		1 => 'Unknown',
		2 => 'Ready',
		3 => 'Failed',
		4 => 'Missing',
		5 => 'Degraded',
	);

	# Check temperature probes on each of the enclosures
	TEMP:
	foreach my $out (@output) {
		if ($snmp) {
			$name = $out->{enclosureTemperatureProbeName} || 'Unknown temp probe';
			$state = get_hashval($out->{enclosureTemperatureProbeState}, \%temp_state) || 'Unknown state';
			$status = get_snmp_probestatus($out->{enclosureTemperatureProbeComponentStatus});
			#$unit      = $out->{temperatureProbeUnit} || 'Unknown unit';
			$reading = $out->{enclosureTemperatureProbeCurValue} || '[N/A]';
			$max_warn = $out->{enclosureTemperatureProbeMaxWarning} || '[N/A]';
			$max_crit = $out->{enclosureTemperatureProbeMaxCritical} || '[N/A]';
			$min_warn = $out->{enclosureTemperatureProbeMinWarning} || '[N/A]';
			$min_crit = $out->{enclosureTemperatureProbeMinCritical} || '[N/A]';
			#$encl_id   = $snmp_enclosure{$out->{temperatureConnectionEnclosureNumber}}{nexus};
			#$encl_name = $out->{temperatureConnectionEnclosureName} || 'Unknown enclosure';
			$nexus = convert_nexus(($out->{enclosureTemperatureProbeFQDD} || 9999));
		}

		next TEMP if blacklisted('encl_temp', $nexus);

		# Make sure these values are integers
		$reading =~ s{\A \s* (-?\d+) \s* C? \s* \z}{$1}xms or $reading = '[N/A]';
		$max_warn =~ s{\A \s* (-?\d+) \s* C? \s* \z}{$1}xms or $max_warn = '[N/A]';
		$max_crit =~ s{\A \s* (-?\d+) \s* C? \s* \z}{$1}xms or $max_crit = '[N/A]';
		$min_warn =~ s{\A \s* (-?\d+) \s* C? \s* \z}{$1}xms or $min_warn = '[N/A]';
		$min_crit =~ s{\A \s* (-?\d+) \s* C? \s* \z}{$1}xms or $min_crit = '[N/A]';

		# Convert temp units
		if ($opt{tempunit} ne 'C') {
			$reading = temp_from_celsius($reading, $opt{tempunit}) if $reading ne '[N/A]';
			$max_warn = temp_from_celsius($max_warn, $opt{tempunit}) if $max_warn ne '[N/A]';
			$max_crit = temp_from_celsius($max_crit, $opt{tempunit}) if $max_crit ne '[N/A]';
			$min_warn = temp_from_celsius($min_warn, $opt{tempunit}) if $min_warn ne '[N/A]';
			$min_crit = temp_from_celsius($min_crit, $opt{tempunit}) if $min_crit ne '[N/A]';
		}

		# Inactive temp probes
		if ($status eq 'Unknown' and $state eq 'Inactive') {
			my $msg = sprintf '%s is %s',
				$name, $state;
			report('storage', $msg, $E_OK, $nexus);
		}
		elsif ($status ne 'Ok' and $reading ne '[N/A]' and $max_crit ne '[N/A]' and $reading > $max_crit) {
			my $msg = sprintf '%s is critically high at %s %s',
				$name, $reading, $opt{tempunit};
			my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
			report('chassis', $msg, $err, $nexus);
		}
		elsif ($status ne 'Ok' and $reading ne '[N/A]' and $max_warn ne '[N/A]' and $reading > $max_warn) {
			my $msg = sprintf '%s is too high at %s %s',
				$name, $reading, $opt{tempunit};
			my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
			report('chassis', $msg, $err, $nexus);
		}
		elsif ($status ne 'Ok' and $reading ne '[N/A]' and $min_crit ne '[N/A]' and $reading < $min_crit) {
			my $msg = sprintf '%s in is critically low at %s %s',
				$name, $reading, $opt{tempunit};
			my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
			report('chassis', $msg, $err, $nexus);
		}
		elsif ($status ne 'Ok' and $reading ne '[N/A]' and $min_warn ne '[N/A]' and $reading < $min_warn) {
			my $msg = sprintf '%s is too low at %s %s',
				$name, $reading, $opt{tempunit};
			my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
			report('chassis', $msg, $err, $nexus);
		}
		# Default
		elsif ($status ne 'Ok') {
			my $msg = sprintf '%s is %s',
				$name, $state;
			if (defined $reading && $reading =~ m{\A -?\d+ \z}xms) {
				# take into account that with certain states the
				# reading doesn't exist or is not an integer
				$msg .= sprintf ' at %s %s', $reading, $opt{tempunit};
				if ($min_warn eq '[N/A]' or $min_crit eq '[N/A]') {
					$msg .= sprintf ' (max=%s/%s)', $max_warn, $max_crit;
				}
				else {
					$msg .= sprintf ' (min=%s/%s, max=%s/%s)',
						$min_warn, $min_crit, $max_warn, $max_crit;
				}
			}
			my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
			report('storage', $msg, $err, $nexus);
		}
		# Ok
		else {
			my $msg = sprintf '%s',
				$name;
			if (defined $reading && $reading ne '[N/A]') {
				# take into account that with certain states the
				# reading doesn't exist or is not an integer
				$msg .= sprintf ' reads %s %s', $reading, $opt{tempunit};
				if ($min_warn eq '[N/A]' or $min_crit eq '[N/A]') {
					$msg .= sprintf ' (max=%s/%s)', $max_warn, $max_crit;
				}
				else {
					$msg .= sprintf ' (min=%s/%s, max=%s/%s)',
						$min_warn, $min_crit, $max_warn, $max_crit;
				}
			}
			else {
				$msg .= sprintf ' is %s', $state;
			}
			report('storage', $msg, $E_OK, $nexus);
		}

		# Collect performance data
		if (defined $opt{perfdata} && $reading ne '[N/A]') {
			my $index = $name;
			$index =~ s{\A Temperature\sProbe\s(\d+) \z}{$1}gxms;
			my $legacy_name = $name;
			$legacy_name =~ s{\A Temperature\sProbe\s(\d+) \z}{temp_$1}gxms;
			#	    my $legacy_label = lc "enclosure_${encl_id}_${legacy_name}";
			#	    my $legacy_mini = $legacy_label;
			#            $legacy_mini =~ s{enclosure_(.+?)_temp_(.+?)}{e$1t$2}xms;
			push @perfdata, {
				type  => 'E',
				id    => $opt{perfdata} eq 'minimal' ? "${index}" : "temp_${index}",
				unit  => $opt{tempunit},
				label => q{},
				#			     legacy => $legacy_label,
				#			     mini   => $legacy_mini,
				value => $reading,
				warn  => $max_warn,
				crit  => $max_crit,
			};
		}
	}
	return;
}


#-----------------------------------------
# STORAGE: Check enclosure management modules (EMM)
#-----------------------------------------
sub check_enclosure_emms {
	return if $#controllers == -1;

	my $nexus = undef;
	my $name = undef;
	my $state = undef;
	my $status = undef;
	my $encl_id = undef;
	my $encl_name = undef;
	my @output = ();

	if ($snmp) {
		my %emms_oid
			= (
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.13.1.2'  => 'enclosureManagementModuleName',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.13.1.4'  => 'enclosureManagementModuleState',
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.13.1.11' => 'enclosureManagementModuleComponentStatus',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.13.1.12' => 'enclosureManagementModuleNexusID', # replaced by enclosureManagementModuleFQDD
			'1.3.6.1.4.1.674.10892.5.5.1.20.130.13.1.15' => 'enclosureManagementModuleFQDD', # was enclosureManagementModuleNexusID
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.14.1.4'  => 'enclosureManagementModuleConnectionEnclosureName',
			#'1.3.6.1.4.1.674.10892.5.5.1.20.130.14.1.5'  => 'enclosureManagementModuleConnectionEnclosureNumber',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $enclosureManagementModuleTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.13';
			#my $enclosureManagementModuleConnectionTable = '1.3.6.1.4.1.674.10892.5.5.1.20.130.14';

			$result = $snmp_session->get_table(-baseoid => $enclosureManagementModuleTable);
			#my $ext = $snmp_session->get_table(-baseoid => $enclosureManagementModuleConnectionTable);

		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %emms_oid ]);
		}

		# No enclosure EMMs is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%emms_oid)};
	}

	## OK - updated for iSM
	my %emms_state
		= (
		1 => 'Unknown',
		2 => 'Ready',
		3 => 'Failed',
		4 => 'Missing',
		5 => 'Degraded',
	);

	# Check EMMs on each of the enclosures
	EMM:
	foreach my $out (@output) {
		if ($snmp) {
			$name = $out->{enclosureManagementModuleName} || 'Unknown EMM';
			$state = get_hashval($out->{enclosureManagementModuleState}, \%emms_state) || 'Unknown state';
			$status = get_snmp_status($out->{enclosureManagementModuleComponentStatus});
			#$encl_id   = $snmp_enclosure{$out->{enclosureManagementModuleConnectionEnclosureNumber}}{nexus};
			#$encl_name = $out->{enclosureManagementModuleConnectionEnclosureName} || 'Unknown enclosure';
			$nexus = convert_nexus(($out->{enclosureManagementModuleFQDD} || 9999));
		}

		next EMM if blacklisted('encl_emm', $nexus);

		# Not installed
		if ($status =~ m{\A Other|Unknown \z}xms and $state eq 'Not Installed') {
			my $msg = sprintf '%s is %s',
				$name, $state;
			report('storage', $msg, $E_OK, $nexus);
		}
		# Default
		else {
			my $msg = sprintf '%s is %s',
				$name, $state;
			report('storage', $msg, $status2nagios{$status}, $nexus);
		}
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check memory modules
#-----------------------------------------
sub check_memory {
	my $index = undef;
	my $status = undef;
	my $location = undef;
	my $size = undef;
	my $modes = undef;
	my @failures = ();
	my @output = ();

	if ($snmp) {
		my %dimm_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.1100.50.1.2.1'  => 'memoryDeviceIndex',
			'1.3.6.1.4.1.674.10892.5.4.1100.50.1.5.1'  => 'memoryDeviceStatus',
			'1.3.6.1.4.1.674.10892.5.4.1100.50.1.8.1'  => 'memoryDeviceLocationName',
			'1.3.6.1.4.1.674.10892.5.4.1100.50.1.14.1' => 'memoryDeviceSize',
			#'1.3.6.1.4.1.674.10892.5.4.1100.50.1.20.1' => 'memoryDeviceFailureModes',
			#'1.3.6.1.4.1.674.10892.5.4.1100.50.1.27.1' => 'memoryDeviceExtendedSize', # is memoryDeviceCurrentOperatingSpeed in iSM, so not used
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $memoryDeviceTable = '1.3.6.1.4.1.674.10892.5.4.1100.50.1';
			$result = $snmp_session->get_table(-baseoid => $memoryDeviceTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %dimm_oid ]);
		}

		if (!defined $result) {
			printf "SNMP ERROR [memory]: %s.\n", $snmp_session->error;
			$snmp_session->close;
			exit $E_UNKNOWN;
		}

		@output = @{get_snmp_output($result, \%dimm_oid)};
	}

	#    # Note: These values are bit masks, so combination values are
	#    # possible. If value is 0 (zero), memory device has no faults.
	#    my %failure_mode
	#      = (
	#	 1  => 'ECC single bit correction warning rate exceeded',
	#	 2  => 'ECC single bit correction failure rate exceeded',
	#	 4  => 'ECC multibit fault encountered',
	#	 8  => 'ECC single bit correction logging disabled',
	#	 16 => 'device disabled because of spare activation',
	#	);

	DIMM:
	foreach my $out (@output) {
		@failures = (); # Initialize
		if ($snmp) {
			$index = ($out->{memoryDeviceIndex} || 10000) - 1;
			$status = get_snmp_status($out->{memoryDeviceStatus});
			$location = $out->{memoryDeviceLocationName} || 'Unknown location';
			$size = (sprintf '%d GB', ($out->{memoryDeviceSize} || 0) / 1024 / 1024);
			#	    $modes    = $out->{memoryDeviceFailureModes} || -9999;
			#	    if ($modes > 0) {
			#		foreach my $mask (sort keys %failure_mode) {
			#		    if (($modes & $mask) != 0) { push @failures, $failure_mode{$mask}; }
			#		}
			#	    }
			#	    elsif ($modes == -9999) {
			#		push @failures, q{ERROR: Failure modes not available via SNMP};
			#	    }
		}
		$location =~ s{\A \s*(.*?)\s* \z}{$1}xms;

		# calculate total memory
		my $msize = defined $size ? $size : 0;
		$msize =~ s{\A (\d+) \s GB}{$1}xms;
		$count{mem} += $msize;

		# Ignore empty memory slots
		next DIMM if !defined $index;

		$count{dimm}++;
		next DIMM if blacklisted('dimm', $index);

		if ($status ne 'Ok') {
			my $msg = undef;
			if (scalar @failures == 0) {
				$msg = sprintf 'Memory module %d [%s, %s] needs attention (%s)',
					$index, $location, $size, $status;
			}
			else {
				$msg = sprintf 'Memory module %d [%s, %s]: %s',
					$index, $location, $size, (join q{, }, @failures);
			}

			report('chassis', $msg, $status2nagios{$status}, $index);
		}
		# Ok
		else {
			my $msg = sprintf 'Memory module %d [%s, %s] is %s',
				$index, $location, $size, $status;
			report('chassis', $msg, $E_OK, $index);
		}
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check fans
#-----------------------------------------
sub check_fans {
	my $index = undef;
	my $status = undef;
	my $reading = undef;
	my $location = undef;
	my $min_crit = undef;
	my $min_warn = undef;
	my @output = ();

	if ($snmp) {
		my %cool_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.700.12.1.2.1'  => 'coolingDeviceIndex',
			'1.3.6.1.4.1.674.10892.5.4.700.12.1.5.1'  => 'coolingDeviceStatus',
			'1.3.6.1.4.1.674.10892.5.4.700.12.1.6.1'  => 'coolingDeviceReading',
			'1.3.6.1.4.1.674.10892.5.4.700.12.1.8.1'  => 'coolingDeviceLocationName',
			#'1.3.6.1.4.1.674.10892.5.4.700.12.1.10.1' => 'coolingDeviceUpperCriticalThreshold',
			#'1.3.6.1.4.1.674.10892.5.4.700.12.1.11.1' => 'coolingDeviceUpperNonCriticalThreshold',
			'1.3.6.1.4.1.674.10892.5.4.700.12.1.12.1' => 'coolingDeviceLowerNonCriticalThreshold',
			'1.3.6.1.4.1.674.10892.5.4.700.12.1.13.1' => 'coolingDeviceLowerCriticalThreshold',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $coolingDeviceTable = '1.3.6.1.4.1.674.10892.5.4.700.12.1';
			$result = $snmp_session->get_table(-baseoid => $coolingDeviceTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %cool_oid ]);
		}

		if ($blade && !defined $result) {
			return 0;
		}
		elsif (!$blade && !defined $result) {
			printf "SNMP ERROR [cooling]: %s.\n", $snmp_session->error;
			$snmp_session->close;
			exit $E_UNKNOWN;
		}

		@output = @{get_snmp_output($result, \%cool_oid)};
	}

	FAN:
	foreach my $out (@output) {
		if ($snmp) {
			$index = ($out->{coolingDeviceIndex} || 10000) - 1;
			$status = get_snmp_probestatus($out->{coolingDeviceStatus});
			$reading = $out->{coolingDeviceReading} || 0;
			$location = $out->{coolingDeviceLocationName} || 'Unknown location';
			$min_crit = $out->{coolingDeviceLowerCriticalThreshold} || 0;
			$min_warn = $out->{coolingDeviceLowerNonCriticalThreshold} || 0;
		}

		$count{fan}++;
		next FAN if blacklisted('fan', $index);

		# Default
		my $msg = sprintf 'Chassis fan %d [%s] reading: %s RPM',
			$index, $location, $reading;
		my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
		report('chassis', $msg, $err, $index);

		# Collect performance data
		if (defined $opt{perfdata}) {
			my $pname = $location;
			$pname =~ s{\s}{_}gxms;
			$pname =~ s{proc_}{cpu#}xms;
			my $legacy_pname = $pname;
			$pname =~ s{_rpm\z}{}ixms;
			push @perfdata, {
				type   => 'F',
				id     => $index,
				unit   => 'rpm',
				label  => $pname,
				legacy => lc "fan_${index}_${legacy_pname}",
				mini   => "f$index",
				value  => $reading,
				warn   => $min_warn,
				crit   => $min_crit,
			};
		}
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check power supplies
#-----------------------------------------
sub check_powersupplies {
	my $index = undef;
	my $status = undef;
	my $type = undef;
	my $err_type = undef;
	my $state = undef;
	my @states = ();
	my @output = ();

	if ($snmp) {
		my %ps_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.600.12.1.2.1'  => 'powerSupplyIndex',
			'1.3.6.1.4.1.674.10892.5.4.600.12.1.5.1'  => 'powerSupplyStatus',
			'1.3.6.1.4.1.674.10892.5.4.600.12.1.7.1'  => 'powerSupplyType',
			'1.3.6.1.4.1.674.10892.5.4.600.12.1.11.1' => 'powerSupplySensorState',
			#'1.3.6.1.4.1.674.10892.5.4.600.12.1.12.1' => 'powerSupplyConfigurationErrorType',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $powerDeviceTable = '1.3.6.1.4.1.674.10892.5.4.600.12.1';
			$result = $snmp_session->get_table(-baseoid => $powerDeviceTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %ps_oid ]);
		}

		# No instrumented PSU is OK (blades, low-end servers)
		return 0 if !defined $result;

		@output = @{get_snmp_output($result, \%ps_oid)};
	}

	## OK - updated for iSM
	my %ps_type
		= (
		1  => 'Other',
		2  => 'Unknown',
		3  => 'Linear',
		4  => 'Switching',
		5  => 'Battery',
		6  => 'Uninterruptible Power Supply',
		7  => 'Converter',
		8  => 'Regulator',
		9  => 'AC',
		10 => 'DC',
		11 => 'VRM',
	);

	## OK - updated for iSM
	my %ps_state
		= (
		1  => 'Presence detected',
		2  => 'Failure detected',
		4  => 'Predictive Failure',
		8  => 'AC lost',
		16 => 'AC lost or out-of-range',
		32 => 'AC out-of-range but present',
		64 => 'Configuration error',
	);

	#    my %ps_config_error_type
	#      = (
	#	 1 => 'Vendor mismatch',
	#	 2 => 'Revision mismatch',
	#	 3 => 'Processor missing',
	#	);

	PS:
	foreach my $out (@output) {
		if ($snmp) {
			@states = (); # contains states for the PS

			$index = ($out->{powerSupplyIndex} || 10000) - 1;
			$status = get_snmp_status($out->{powerSupplyStatus});
			$type = get_hashval($out->{powerSupplyType}, \%ps_type) || 'Unknown type';
			#$err_type = get_hashval($out->{powerSupplyConfigurationErrorType}, \%ps_config_error_type);

			# get the combined state from the StatusReading OID
			my $raw_state = $out->{powerSupplySensorState} || 0;
			foreach my $mask (sort keys %ps_state) {
				if (($raw_state & $mask) != 0) {
					push @states, $ps_state{$mask};
				}
			}

			# If configuration error, also include the error type
			#	    if (defined $err_type) {
			#		push @states, $err_type;
			#	    }

			# Finally, construct the state string
			$state = join q{, }, @states;
		}
		else {
			$index = get_nonempty_string('Index', $out, 9999);
			$status = get_nonempty_string('Status', $out, 'Unknown');
			$type = get_nonempty_string('Type', $out, 'Unknown type');
			$state = get_nonempty_string('Online Status', $out, 'Unknown state');
		}

		$count{power}++;
		next PS if blacklisted('ps', $index);

		my $msg = sprintf 'Power Supply %d [%s]: %s',
			$index, $type, $state;
		report('chassis', $msg, $status2nagios{$status}, $index);
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check temperatures
#-----------------------------------------
sub check_temperatures {
	my $index = undef;
	my $status = undef;
	my $reading = undef;
	my $location = undef;
	my $max_crit = undef;
	my $max_warn = undef;
	my $min_warn = undef;
	my $min_crit = undef;
	my $type = undef;
	my $discrete = undef;
	my @output = ();

	# Getting custom temperature thresholds (user option)
	my %warn_threshold = %{custom_temperature_thresholds('w')};
	my %crit_threshold = %{custom_temperature_thresholds('c')};

	if ($snmp) {
		my %temp_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.2.1'  => 'temperatureProbeIndex',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.5.1'  => 'temperatureProbeStatus',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.6.1'  => 'temperatureProbeReading',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.7.1'  => 'temperatureProbeType',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.8.1'  => 'temperatureProbeLocationName',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.10.1' => 'temperatureProbeUpperCriticalThreshold',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.11.1' => 'temperatureProbeUpperNonCriticalThreshold',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.12.1' => 'temperatureProbeLowerNonCriticalThreshold',
			'1.3.6.1.4.1.674.10892.5.4.700.20.1.13.1' => 'temperatureProbeLowerCriticalThreshold',
			#'1.3.6.1.4.1.674.10892.5.4.700.20.1.16.1' => 'temperatureProbeDiscreteReading',
		);
		# this didn't work well for some reason
		my $result = $snmp_session->get_entries(-columns => [ keys %temp_oid ]);

		# Getting values using the table
		my $temperatureProbeTable = '1.3.6.1.4.1.674.10892.5.4.700.20';
		#my $result = $snmp_session->get_table(-baseoid => $temperatureProbeTable);

		if (!defined $result) {
			printf "SNMP ERROR [temperatures]: %s.\n", $snmp_session->error;
			$snmp_session->close;
			exit $E_UNKNOWN;
		}

		@output = @{get_snmp_output($result, \%temp_oid)};
	}

	## OK - updated for iSM
	my %probe_type
		= (
		1  => 'Other',      # type is other than following values
		2  => 'Unknown',    # type is unknown
		3  => 'AmbientESM', # type is Ambient Embedded Systems Management temperature probe
		16 => 'Discrete',   # type is temperature probe with discrete reading
	);

	TEMP:
	foreach my $out (@output) {
		if ($snmp) {
			$index = ($out->{temperatureProbeIndex} || 10000) - 1;
			$status = get_snmp_probestatus($out->{temperatureProbeStatus});
			$location = $out->{temperatureProbeLocationName} || 'Unknown location';
			$type = get_hashval($out->{temperatureProbeType}, \%probe_type);
			$reading = $out->{temperatureProbeReading} || '[N/A]';
			$max_crit = $out->{temperatureProbeUpperCriticalThreshold} || '[N/A]';
			$max_warn = $out->{temperatureProbeUpperNonCriticalThreshold} || '[N/A]';
			$min_crit = $out->{temperatureProbeLowerCriticalThreshold} || '[N/A]';
			$min_warn = $out->{temperatureProbeLowerNonCriticalThreshold} || '[N/A]';
			#$discrete = $out->{temperatureProbeDiscreteReading} || '[N/A]';

			# If numeric values, i.e. not discrete
			$reading /= 10 if $reading =~ m{\A -?\d+ \z}xms;
			$max_crit /= 10 if $max_crit =~ m{\A -?\d+ \z}xms;
			$max_warn /= 10 if $max_warn =~ m{\A -?\d+ \z}xms;
			$min_crit /= 10 if $min_crit =~ m{\A -?\d+ \z}xms;
			$min_warn /= 10 if $min_warn =~ m{\A -?\d+ \z}xms;

			# workaround for bad temp probes
			if ($type eq 'AmbientESM' and $reading !~ m{\A \d+(\.\d+)? \z}xms) {
				$type = 'Discrete';
			}
		}

		$count{temp}++;
		next TEMP if blacklisted('temp', $index);

		# Convert temp units
		if ($opt{tempunit} ne 'C') {
			$reading = temp_from_celsius($reading, $opt{tempunit}) if $reading ne '[N/A]';
			$max_warn = temp_from_celsius($max_warn, $opt{tempunit}) if $max_warn ne '[N/A]';
			$max_crit = temp_from_celsius($max_crit, $opt{tempunit}) if $max_crit ne '[N/A]';
			$min_warn = temp_from_celsius($min_warn, $opt{tempunit}) if $min_warn ne '[N/A]';
			$min_crit = temp_from_celsius($min_crit, $opt{tempunit}) if $min_crit ne '[N/A]';
		}
		else {
			# First check according to custom thresholds
			if (exists $crit_threshold{$index}{max} and $reading > $crit_threshold{$index}{max}) {
				# Custom critical MAX
				my $msg = sprintf 'Temperature Probe %d [%s] reads %s %s (custom max=%s)',
					$index, $location, $reading, $opt{tempunit}, $crit_threshold{$index}{max};
				report('chassis', $msg, $E_CRITICAL, $index);
			}
			elsif (exists $warn_threshold{$index}{max} and $reading > $warn_threshold{$index}{max}) {
				# Custom warning MAX
				my $msg = sprintf 'Temperature Probe %d [%s] reads %s %s (custom max=%s)',
					$index, $location, $reading, $opt{tempunit}, $warn_threshold{$index}{max};
				report('chassis', $msg, $E_WARNING, $index);
			}
			elsif (exists $crit_threshold{$index}{min} and $reading < $crit_threshold{$index}{min}) {
				# Custom critical MIN
				my $msg = sprintf 'Temperature Probe %d [%s] reads %s %s (custom min=%s)',
					$index, $location, $reading, $opt{tempunit}, $crit_threshold{$index}{min};
				report('chassis', $msg, $E_CRITICAL, $index);
			}
			elsif (exists $warn_threshold{$index}{min} and $reading < $warn_threshold{$index}{min}) {
				# Custom warning MIN
				my $msg = sprintf 'Temperature Probe %d [%s] reads %s %s (custom min=%s)',
					$index, $location, $reading, $opt{tempunit}, $warn_threshold{$index}{min};
				report('chassis', $msg, $E_WARNING, $index);
			}
			elsif ($status ne 'Ok' and $max_crit ne '[N/A]' and $reading > $max_crit) {
				my $msg = sprintf 'Temperature Probe %d [%s] is critically high at %s %s',
					$index, $location, $reading, $opt{tempunit};
				my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
				report('chassis', $msg, $err, $index);
			}
			elsif ($status ne 'Ok' and $max_warn ne '[N/A]' and $reading > $max_warn) {
				my $msg = sprintf 'Temperature Probe %d [%s] is too high at %s %s',
					$index, $location, $reading, $opt{tempunit};
				my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
				report('chassis', $msg, $err, $index);
			}
			elsif ($status ne 'Ok' and $min_crit ne '[N/A]' and $reading < $min_crit) {
				my $msg = sprintf 'Temperature Probe %d [%s] is critically low at %s %s',
					$index, $location, $reading, $opt{tempunit};
				my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
				report('chassis', $msg, $err, $index);
			}
			elsif ($status ne 'Ok' and $min_warn ne '[N/A]' and $reading < $min_warn) {
				my $msg = sprintf 'Temperature Probe %d [%s] is too low at %s %s',
					$index, $location, $reading, $opt{tempunit};
				my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
				report('chassis', $msg, $err, $index);
			}
			# Ok
			else {
				my $msg = sprintf 'Temperature Probe %d [%s] reads %s %s',
					$index, $location, $reading, $opt{tempunit};
				if ($min_warn eq '[N/A]' and $min_crit eq '[N/A]') {
					$msg .= sprintf ' (max=%s/%s)', $max_warn, $max_crit;
				}
				else {
					$msg .= sprintf ' (min=%s/%s, max=%s/%s)',
						$min_warn, $min_crit, $max_warn, $max_crit;
				}
				my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
				report('chassis', $msg, $err, $index);
			}

			# Collect performance data
			if (defined $opt{perfdata}) {
				my $pname = $location;
				$pname =~ s{\s}{_}gxms;
				$pname =~ s{_temp\z}{}ixms;
				$pname =~ s{proc_}{cpu#}xms;
				push @perfdata, {
					type   => 'T',
					id     => $index,
					unit   => $opt{tempunit},
					label  => $pname,
					legacy => lc "temp_${index}_${pname}",
					mini   => "t$index",
					value  => $reading,
					warn   => $max_warn,
					crit   => $max_crit,
				};
			}
		}
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check processors
#-----------------------------------------
sub check_processors {
	my $index = undef;
	my $status = undef;
	my $state = undef;
	my $brand = undef;
	my $family = undef;
	my $man = undef;
	my $speed = undef;
	my @output = ();

	if ($snmp) {

		# NOTE: For some reason, older models don't have the
		# "Processor Device Status" OIDs. We check both the newer
		# (preferred) OIDs and the old ones.

		my %cpu_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.1100.30.1.2.1'  => 'processorDeviceIndex',
			'1.3.6.1.4.1.674.10892.5.4.1100.30.1.5.1'  => 'processorDeviceStatus',
			'1.3.6.1.4.1.674.10892.5.4.1100.30.1.8.1'  => 'processorDeviceManufacturerName',
			'1.3.6.1.4.1.674.10892.5.4.1100.30.1.9.1'  => 'processorDeviceStatusState',
			'1.3.6.1.4.1.674.10892.5.4.1100.30.1.10.1' => 'processorDeviceFamily',
			'1.3.6.1.4.1.674.10892.5.4.1100.30.1.12.1' => 'processorDeviceCurrentSpeed',
			'1.3.6.1.4.1.674.10892.5.4.1100.30.1.23.1' => 'processorDeviceBrandName',
			'1.3.6.1.4.1.674.10892.5.4.1100.32.1.2.1'  => 'processorDeviceStatusIndex',
			'1.3.6.1.4.1.674.10892.5.4.1100.32.1.5.1'  => 'processorDeviceStatusStatus',
			'1.3.6.1.4.1.674.10892.5.4.1100.32.1.6.1'  => 'processorDeviceStatusReading',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $processorDeviceTable = '1.3.6.1.4.1.674.10892.5.4.1100.30.1';
			my $processorDeviceStatusTable = '1.3.6.1.4.1.674.10892.5.4.1100.32.1';

			$result = $snmp_session->get_table(-baseoid => $processorDeviceTable);
			my $ext = $snmp_session->get_table(-baseoid => $processorDeviceStatusTable);

			defined $ext && map {$$result{$_} = $$ext{$_}} keys %{$ext};
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %cpu_oid ]);
		}

		if (!defined $result) {
			printf "SNMP ERROR [processors]: %s.\n", $snmp_session->error;
			$snmp_session->close;
			exit $E_UNKNOWN;
		}

		@output = @{get_snmp_output($result, \%cpu_oid)};
	}

	## OK - updated for iSM
	my %cpu_state
		= (
		1 => 'Other',         # other than following values
		2 => 'Unknown',       # unknown
		3 => 'Enabled',       # enabled
		4 => 'User Disabled', # disabled by user via BIOS setup
		5 => 'BIOS Disabled', # disabled by BIOS (POST error)
		6 => 'Idle',          # idle
	);

	## OK - updated for iSM
	my %cpu_reading
		= (
		1    => 'Internal Error',      # Internal Error
		2    => 'Thermal Trip',        # Thermal Trip
		32   => 'Configuration Error', # Configuration Error
		128  => 'Present',             # Processor Present
		256  => 'Disabled',            # Processor Disabled
		512  => 'Terminator Present',  # Terminator Present
		1024 => 'Throttled',           # Processor Throttled
	);

	## OK - updated for iSM
	# Mapping between family numbers from SNMP and actual CPU family
	my %cpu_family
		= (
		1   => 'Other', 2 => 'Unknown',
		3   => '8086', 4 => '80286',
		5   => '386', 6 => '486',
		7   => '8087', 8 => '80287',
		9   => '80387', 10 => '80487',
		11  => 'Pentium', 12 => 'Pentium Pro',
		13  => 'Pentium II', 14 => 'Pentium with MMX',
		15  => 'Celeron', 16 => 'Pentium II Xeon',
		17  => 'Pentium III', 18 => 'Pentium III Xeon',
		19  => 'Pentium III', 20 => 'Itanium',
		21  => 'Xeon', 22 => 'Pentium 4',
		23  => 'Xeon MP', 24 => 'Itanium 2',
		25  => 'K5', 26 => 'K6',
		27  => 'K6-2', 28 => 'K6-3',
		29  => 'Athlon', 30 => 'AMD2900',
		31  => 'K6-2+', 32 => 'Power PC',
		33  => 'Power PC 601', 34 => 'Power PC 603',
		35  => 'Power PC 603+', 36 => 'Power PC 604',
		37  => 'Power PC 620', 38 => 'Power PC x704',
		39  => 'Power PC 750', 40 => 'Core Duo',
		41  => 'Core Duo mobile', 42 => 'Core Solo mobile',
		43  => 'Intel Atom', 44 => undef,
		45  => undef, 46 => undef,
		47  => undef, 48 => 'Alpha',
		49  => 'Alpha 21064', 50 => 'Alpha 21066',
		51  => 'Alpha 21164', 52 => 'Alpha 21164PC',
		53  => 'Alpha 21164a', 54 => 'Alpha 21264',
		55  => 'Alpha 21364', 56 => 'Turion II Ultra Dual-Core Mobile M',
		57  => 'Turion II Dual-Core Mobile M', 58 => 'Athlon II Dual-Core Mobile M ',
		59  => 'Opteron 6100', 60 => 'Opteron 4100',
		61  => undef, 62 => undef,
		63  => undef, 64 => 'MIPS',
		65  => 'MIPS R4000', 66 => 'MIPS R4200',
		67  => 'MIPS R4400', 68 => 'MIPS R4600',
		69  => 'MIPS R10000', 70 => undef,
		71  => undef, 72 => undef,
		73  => undef, 74 => undef,
		75  => undef, 76 => undef,
		77  => undef, 78 => undef,
		79  => undef, 80 => 'SPARC',
		81  => 'SuperSPARC', 82 => 'microSPARC II',
		83  => 'microSPARC IIep', 84 => 'UltraSPARC',
		85  => 'UltraSPARC II', 86 => 'UltraSPARC IIi',
		87  => 'UltraSPARC III', 88 => 'UltraSPARC IIIi',
		89  => undef, 90 => undef,
		91  => undef, 92 => undef,
		93  => undef, 94 => undef,
		95  => undef, 96 => '68040',
		97  => '68xxx', 98 => '68000',
		99  => '68010', 100 => '68020',
		101 => '68030', 102 => undef,
		103 => undef, 104 => undef,
		105 => undef, 106 => undef,
		107 => undef, 108 => undef,
		109 => undef, 110 => undef,
		111 => undef, 112 => 'Hobbit',
		113 => undef, 114 => undef,
		115 => undef, 116 => undef,
		117 => undef, 118 => undef,
		119 => undef, 120 => 'Crusoe TM5000',
		121 => 'Crusoe TM3000', 122 => 'Efficeon TM8000',
		123 => undef, 124 => undef,
		125 => undef, 126 => undef,
		127 => undef, 128 => 'Weitek',
		129 => undef, 130 => 'Celeron M',
		131 => 'Athlon 64', 132 => 'Opteron',
		133 => 'Sempron', 134 => 'Turion 64 Mobile',
		135 => 'Dual-Core Opteron', 136 => 'Athlon 64 X2 DC',
		137 => 'Turion 64 X2 M', 138 => 'Quad-Core Opteron',
		139 => '3rd gen Opteron', 140 => 'AMD Phenom FX Quad-Core',
		141 => 'AMD Phenom X4 Quad-Core', 142 => 'AMD Phenom X2 Dual-Core',
		143 => 'AMD Athlon X2 Dual-Core', 144 => 'PA-RISC',
		145 => 'PA-RISC 8500', 146 => 'PA-RISC 8000',
		147 => 'PA-RISC 7300LC', 148 => 'PA-RISC 7200',
		149 => 'PA-RISC 7100LC', 150 => 'PA-RISC 7100',
		151 => undef, 152 => undef,
		153 => undef, 154 => undef,
		155 => undef, 156 => undef,
		157 => undef, 158 => undef,
		159 => undef, 160 => 'V30',
		161 => 'Quad-Core Xeon 3200', 162 => 'Dual-Core Xeon 3000',
		163 => 'Quad-Core Xeon 5300', 164 => 'Dual-Core Xeon 5100',
		165 => 'Dual-Core Xeon 5000', 166 => 'Dual-Core Xeon LV',
		167 => 'Dual-Core Xeon ULV', 168 => 'Dual-Core Xeon 7100',
		169 => 'Quad-Core Xeon 5400', 170 => 'Quad-Core Xeon',
		171 => 'Dual-Core Xeon 5200', 172 => 'Dual-Core Xeon 7200',
		173 => 'Quad-Core Xeon 7300', 174 => 'Quad-Core Xeon 7400',
		175 => 'Multi-Core Xeon 7400', 176 => 'M1',
		177 => 'M2', 178 => undef,
		179 => 'Pentium 4 HT', 180 => 'AS400',
		181 => undef, 182 => 'Athlon XP',
		183 => 'Athlon MP', 184 => 'Duron',
		185 => 'Pentium M', 186 => 'Celeron D',
		187 => 'Pentium D', 188 => 'Pentium Extreme',
		189 => 'Core Solo', 190 => 'Core2',
		191 => 'Core2 Duo', 192 => 'Core2 Solo',
		193 => 'Core2 Extreme', 194 => 'Core2 Quad',
		195 => 'Core2 Extreme mobile', 196 => 'Core2 Duo mobile',
		197 => 'Core2 Solo mobile', 198 => 'Core i7',
		199 => 'Dual-Core Celeron', 200 => 'IBM390',
		201 => 'G4', 202 => 'G5',
		203 => 'ESA/390 G6', 204 => 'z/Architectur',
		205 => 'Core i5', 206 => 'Core i3',
		207 => undef, 208 => undef,
		209 => undef, 210 => 'C7-M',
		211 => 'C7-D', 212 => 'C7',
		213 => 'Eden', 214 => 'Multi-Core Xeon',
		215 => 'Dual-Core Xeon 3xxx', 216 => 'Quad-Core Xeon 3xxx',
		217 => 'VIA Nano', 218 => 'Dual-Core Xeon 5xxx',
		219 => 'Quad-Core Xeon 5xxx', 220 => undef,
		221 => 'Dual-Core Xeon 7xxx', 222 => 'Quad-Core Xeon 7xxx',
		223 => 'Multi-Core Xeon 7xxx', 224 => 'Multi-Core Xeon 3400',
		225 => undef, 226 => undef,
		227 => undef, 228 => undef,
		229 => undef, 230 => 'Embedded AMD Opteron Quad-Core',
		231 => 'AMD Phenom Triple-Core', 232 => 'AMD Turion Ultra Dual-Core Mobile',
		233 => 'AMD Turion Dual-Core Mobile', 234 => 'AMD Athlon Dual-Core',
		235 => 'AMD Sempron SI', 236 => 'AMD Phenom II',
		237 => 'AMD Athlon II', 238 => 'Six-Core AMD Opteron',
		239 => 'AMD Sempron M', 240 => undef,
		241 => undef, 242 => undef,
		243 => undef, 244 => undef,
		245 => undef, 246 => undef,
		247 => undef, 248 => undef,
		249 => undef, 250 => 'i860',
		251 => 'i960',
	);

	CPU:
	foreach my $out (@output) {
		if ($snmp) {
			$index = exists $out->{processorDeviceStatusIndex}
				? ($out->{processorDeviceStatusIndex} || 10000) - 1
				: ($out->{processorDeviceIndex} || 10000) - 1;
			$status = exists $out->{processorDeviceStatusStatus}
				? get_snmp_status($out->{processorDeviceStatusStatus})
				: get_snmp_status($out->{processorDeviceStatus});
			if (defined $out->{processorDeviceStatusReading}) {
				my @states = (); # contains states for the CPU

				# get the combined state from the StatusReading OID
				foreach my $mask (sort keys %cpu_reading) {
					if (($out->{processorDeviceStatusReading} & $mask) != 0) {
						push @states, $cpu_reading{$mask};
					}
				}

				# Finally, create the state string
				$state = join q{, }, @states;
			}
			else {
				$state = get_hashval($out->{processorDeviceStatusState}, \%cpu_state) || 'Unknown state';
			}
			$man = $out->{processorDeviceManufacturerName} || undef;
			$family = (defined $out->{processorDeviceFamily}
				and defined $cpu_family{$out->{processorDeviceFamily}})
				? $cpu_family{$out->{processorDeviceFamily}} : undef;
			$speed = $out->{processorDeviceCurrentSpeed} || undef;
			$brand = $out->{processorDeviceBrandName} || undef;
		}

		# Ignore unoccupied CPU slots (snmp)
		if ($snmp and defined $out->{processorDeviceStatusReading}
			and $out->{processorDeviceStatusReading} == 0) {
			next CPU;
		}

		$count{cpu}++;
		next CPU if blacklisted('cpu', $index);

		if (defined $brand) {
			$brand =~ s{\s\s+}{ }gxms;
			$brand =~ s{\((R|tm)\)}{}gxms;
			$brand =~ s{\s(CPU|Processor)}{}xms;
			$brand =~ s{\s\@}{}xms;
		}
		elsif (defined $family and defined $man and defined $speed) {
			$speed =~ s{\A (\d+) .*}{$1}xms;
			$brand = sprintf '%s %s %.2fGHz', $man, $family, $speed / 1000;
		}
		else {
			$brand = "unknown";
		}

		# Default
		my $msg = sprintf 'Processor %d [%s] is %s',
			$index, $brand, $state;
		report('chassis', $msg, $status2nagios{$status}, $index);
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check voltage probes
#-----------------------------------------
sub check_volts {
	my $index = undef;
	my $status = undef;
	my $reading = undef;
	my $location = undef;
	my $max_crit = undef;
	my $max_warn = undef;
	my @output = ();

	if ($snmp) {
		my %volt_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.600.20.1.2.1'  => 'voltageProbeIndex',
			'1.3.6.1.4.1.674.10892.5.4.600.20.1.5.1'  => 'voltageProbeStatus',
			'1.3.6.1.4.1.674.10892.5.4.600.20.1.6.1'  => 'voltageProbeReading',
			'1.3.6.1.4.1.674.10892.5.4.600.20.1.8.1'  => 'voltageProbeLocationName',
			'1.3.6.1.4.1.674.10892.5.4.600.20.1.16.1' => 'voltageProbeDiscreteReading',
		);

		my $voltageProbeTable = '1.3.6.1.4.1.674.10892.5.4.600.20.1';
		my $result = $snmp_session->get_table(-baseoid => $voltageProbeTable);

		if (!defined $result) {
			printf "SNMP ERROR [voltage]: %s.\n", $snmp_session->error;
			$snmp_session->close;
			exit $E_UNKNOWN;
		}

		@output = @{get_snmp_output($result, \%volt_oid)};
	}

	## OK - updated for iSM
	my %volt_discrete_reading
		= (
		1 => 'Good',
		2 => 'Bad',
	);

	VOLT:
	foreach my $out (@output) {
		if ($snmp) {
			$index = ($out->{voltageProbeIndex} || 10000) - 1;
			$status = get_snmp_probestatus($out->{voltageProbeStatus});
			$reading = defined $out->{voltageProbeReading}
				? sprintf('%.3f V', $out->{voltageProbeReading} / 1000)
				: (get_hashval($out->{voltageProbeDiscreteReading}, \%volt_discrete_reading) || 'Unknown reading');
			$location = $out->{voltageProbeLocationName} || 'Unknown location';
			$max_crit = $out->{voltageProbeUpperCriticalThreshold} || 0;
			$max_warn = $out->{voltageProbeUpperNonCriticalThreshold} || 0;
		}

		$count{volt}++;
		next VOLT if blacklisted('volt', $index);

		# remove trailing zeroes (if reading is an integer)
		$reading =~ s{\A (\d+)\.000\sV \z}{$1 V}xms;

		my $msg = undef;
		if ($reading =~ m{\A \d+(:?\.\d+)?\sV \z}xms) {
			# number reading
			$msg = sprintf 'Voltage sensor %d [%s] reads %s',
				$index, $location, $reading;
		}
		else {
			# discrete reading
			$msg = sprintf 'Voltage sensor %d [%s] is %s',
				$index, $location, $reading;
		}
		my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
		report('chassis', $msg, $err, $index);

		# Collect performance data
		if (defined $opt{perfdata} and !$opt{legacy_perfdata}) {
			$reading =~ s{\s+V\z}{}xms;                       # remove unit
			$reading =~ s{\.000\z}{}xms;                      # if integer
			next VOLT if $reading !~ m{\A \d+(\.\d+)? \z}xms; # discrete reading (not number)
			my $label = join q{_}, $location;
			$label =~ s{\s}{_}gxms;
			push @perfdata, {
				type  => 'V',
				id    => $index,
				unit  => 'V',
				label => $label,
				value => $reading,
				warn  => 0,
				crit  => 0,
			};
		}
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check batteries
#-----------------------------------------
sub check_batteries {
	my $index = undef;
	my $status = undef;
	my $reading = undef;
	my $location = undef;
	my @output = ();

	if ($snmp) {
		my %bat_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.600.50.1.2.1' => 'systemBatteryIndex',
			'1.3.6.1.4.1.674.10892.5.4.600.50.1.5.1' => 'systemBatteryStatus',
			'1.3.6.1.4.1.674.10892.5.4.600.50.1.6.1' => 'systemBatteryReading',
			'1.3.6.1.4.1.674.10892.5.4.600.50.1.7.1' => 'systemBatteryLocationName',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $batteryTable = '1.3.6.1.4.1.674.10892.5.4.600.50.1';
			$result = $snmp_session->get_table(-baseoid => $batteryTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %bat_oid ]);
		}

		# No batteries is OK
		return 0 if !defined $result;

		@output = @{get_snmp_output($result, \%bat_oid)};
	}

	## OK - updated for iSM
	my %bat_reading
		= (
		1 => 'Predictive Failure',
		2 => 'Failed',
		4 => 'Presence Detected',
	);

	BATTERY:
	foreach my $out (@output) {
		if ($snmp) {
			$index = ($out->{systemBatteryIndex} || 10000) - 1;
			$status = get_snmp_status($out->{systemBatteryStatus});
			$reading = get_hashval($out->{systemBatteryReading}, \%bat_reading) || 'Unknown reading';
			$location = $out->{systemBatteryLocationName} || 'Unknown location';
		}

		$count{bat}++;
		next BATTERY if blacklisted('bp', $index);

		my $msg = sprintf 'Battery probe %d [%s] is %s',
			$index, $location, $reading;
		report('chassis', $msg, $status2nagios{$status}, $index);
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check amperage probes (power monitoring)
#-----------------------------------------
sub check_pwrmonitoring {
	my $index = undef;
	my $status = undef;
	my $reading = undef;
	my $location = undef;
	my $max_crit = undef;
	my $max_warn = undef;
	my $unit = undef;
	my $type = undef;
	my @output = ();

	if ($snmp) {
		my %amp_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.600.30.1.2.1'  => 'amperageProbeIndex',
			'1.3.6.1.4.1.674.10892.5.4.600.30.1.5.1'  => 'amperageProbeStatus',
			'1.3.6.1.4.1.674.10892.5.4.600.30.1.6.1'  => 'amperageProbeReading',
			'1.3.6.1.4.1.674.10892.5.4.600.30.1.7.1'  => 'amperageProbeType',
			'1.3.6.1.4.1.674.10892.5.4.600.30.1.8.1'  => 'amperageProbeLocationName',
			'1.3.6.1.4.1.674.10892.5.4.600.30.1.10.1' => 'amperageProbeUpperCriticalThreshold',
			'1.3.6.1.4.1.674.10892.5.4.600.30.1.11.1' => 'amperageProbeUpperNonCriticalThreshold',
			#'1.3.6.1.4.1.674.10892.5.4.600.30.1.16.1' => 'amperageProbeDiscreteReading',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $amperageProbeTable = '1.3.6.1.4.1.674.10892.5.4.600.30.1';
			$result = $snmp_session->get_table(-baseoid => $amperageProbeTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %amp_oid ]);
		}

		# No pwrmonitoring is OK
		return 0 if !defined $result;

		@output = @{get_snmp_output($result, \%amp_oid)};
	}

	## OK - updated for iSM
	my %amp_type # Amperage probe types
		= (
		1  => 'amperageProbeTypeIsOther',            # other than following values
		2  => 'amperageProbeTypeIsUnknown',          # unknown
		3  => 'amperageProbeTypeIs1Point5Volt',      # 1.5 amperage probe
		4  => 'amperageProbeTypeIs3Point3volt',      # 3.3 amperage probe
		5  => 'amperageProbeTypeIs5Volt',            # 5 amperage probe
		6  => 'amperageProbeTypeIsMinus5Volt',       # -5 amperage probe
		7  => 'amperageProbeTypeIs12Volt',           # 12 amperage probe
		8  => 'amperageProbeTypeIsMinus12Volt',      # -12 amperage probe
		9  => 'amperageProbeTypeIsIO',               # I/O probe
		10 => 'amperageProbeTypeIsCore',             # Core probe
		11 => 'amperageProbeTypeIsFLEA',             # FLEA (standby) probe
		12 => 'amperageProbeTypeIsBattery',          # Battery probe
		13 => 'amperageProbeTypeIsTerminator',       # SCSI Termination probe
		14 => 'amperageProbeTypeIs2Point5Volt',      # 2.5 amperage probe
		15 => 'amperageProbeTypeIsGTL',              # GTL (ground termination logic) probe
		16 => 'amperageProbeTypeIsDiscrete',         # amperage probe with discrete reading
		23 => 'amperageProbeTypeIsPowerSupplyAmps',  # Power Supply probe with reading in Amps
		24 => 'amperageProbeTypeIsPowerSupplyWatts', # Power Supply probe with reading in Watts
		25 => 'amperageProbeTypeIsSystemAmps',       # System probe with reading in Amps
		26 => 'amperageProbeTypeIsSystemWatts',      # System probe with reading in Watts
	);

	## OK - updated for iSM
	my %amp_discrete
		= (
		1 => 'Good',
		2 => 'Bad',
	);

	my %amp_unit
		= (
		'amperageProbeTypeIsPowerSupplyAmps'  => 'hA', # tenths of Amps
		'amperageProbeTypeIsSystemAmps'       => 'hA', # tenths of Amps
		'amperageProbeTypeIsPowerSupplyWatts' => 'W',  # Watts
		'amperageProbeTypeIsSystemWatts'      => 'W',  # Watts
		'amperageProbeTypeIsDiscrete'         => q{},  # discrete reading, no unit
	);

	AMP:
	foreach my $out (@output) {
		if ($snmp) {
			$index = ($out->{amperageProbeIndex} || 10000) - 1;
			$status = get_snmp_probestatus($out->{amperageProbeStatus});
			$type = get_hashval($out->{amperageProbeType}, \%amp_type);
			$reading = ($out->{amperageProbeReading} || 0);
			$location = $out->{amperageProbeLocationName} || 'Unknown location';
			$max_crit = $out->{amperageProbeUpperCriticalThreshold} || 0;
			$max_warn = $out->{amperageProbeUpperNonCriticalThreshold} || 0;
			$unit = exists $amp_unit{$amp_type{$out->{amperageProbeType}}}
				? $amp_unit{$amp_type{$out->{amperageProbeType}}} : 'mA';

			# calculate proper values and set unit for ampere probes
			if ($unit eq 'hA' and $type ne 'amperageProbeTypeIsDiscrete') {
				$reading /= 10;
				$max_crit /= 10;
				$max_warn /= 10;
				$unit = 'A';
			}
			if ($unit eq 'mA' and $type ne 'amperageProbeTypeIsDiscrete') {
				$reading /= 1000;
				$max_crit /= 1000;
				$max_warn /= 1000;
				$unit = 'A';
			}
		}

		next AMP if $index !~ m{\A \d+ \z}xms;

		# Special case: Probe is present but unknown. This happens via
		# SNMP on some systems where power monitoring capability is
		# disabled due to non-redundant and/or non-instrumented power
		# supplies.
		# E.g. R410 with newer BMC firmware and 1 power supply
		if ($snmp && $type ne 'amperageProbeTypeIsDiscrete' && $status eq 'Unknown' && $reading == 0) {
			next AMP;
		}

		$count{amp}++;
		next AMP if blacklisted('amp', $index);

		# Special case: Discrete reading
		if (defined $type and $type eq 'amperageProbeTypeIsDiscrete') {
			my $msg = sprintf 'Amperage probe %d [%s] is %s',
				$index, $location, $reading;
			my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
			report('chassis', $msg, $err, $index);
		}
		# Default
		else {
			my $msg = sprintf 'Amperage probe %d [%s] reads %s %s',
				$index, $location, $reading, $unit;
			my $err = $snmp ? $probestatus2nagios{$status} : $status2nagios{$status};
			report('chassis', $msg, $err, $index);
		}

		# Collect performance data
		if (defined $opt{perfdata}) {
			next AMP if $reading !~ m{\A \d+(\.\d+)? \z}xms; # discrete reading (not number)
			my $label = join q{_}, $location;
			$label =~ s{\s}{_}gxms;
			push @perfdata, {
				type   => $unit,
				id     => $index,
				unit   => $unit,
				label  => $label,
				legacy => (join q{_}, 'pwr_mon', $index, lc $label),
				mini   => "p${index}" . lc $unit,
				value  => $reading,
				warn   => $max_warn,
				crit   => $max_crit,
			};
		}
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check intrusion
#-----------------------------------------
sub check_intrusion {
	my $index = undef;
	my $status = undef;
	my $reading = undef;
	my @output = ();

	if ($snmp) {
		my %int_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.300.70.1.2.1' => 'intrusionIndex',
			'1.3.6.1.4.1.674.10892.5.4.300.70.1.5.1' => 'intrusionStatus',
			'1.3.6.1.4.1.674.10892.5.4.300.70.1.6.1' => 'intrusionReading',
		);
		my $result = undef;
		if ($opt{use_get_table}) {
			my $intrusionTable = '1.3.6.1.4.1.674.10892.5.4.300.70.1';
			$result = $snmp_session->get_table(-baseoid => $intrusionTable);
		}
		else {
			$result = $snmp_session->get_entries(-columns => [ keys %int_oid ]);
		}

		# No intrusion is OK
		return 0 if !defined $result;

		@output = @{get_snmp_output($result, \%int_oid)};
	}

	## OK - updated for iSM
	my %int_reading
		= (
		1 => 'Not Breached',          # chassis not breached and no uncleared breaches
		2 => 'Breached',              # chassis currently breached
		3 => 'Breached Prior',        # chassis breached prior to boot and has not been cleared
		4 => 'Breach Sensor Failure', # intrusion sensor has failed
	);

	INTRUSION:
	foreach my $out (@output) {
		if ($snmp) {
			$index = ($out->{intrusionIndex} || 10000) - 1;
			$status = get_snmp_status($out->{intrusionStatus});
			$reading = get_hashval($out->{intrusionReading}, \%int_reading) || 'Unknown reading';
		}

		$count{intr}++;
		next INTRUSION if blacklisted('intr', $index);

		if ($status ne 'Ok') {
			my $msg = sprintf 'Chassis intrusion %d detected: %s',
				$index, $reading;
			report('chassis', $msg, $E_WARNING, $index);
		}
		# Ok
		else {
			my $msg = sprintf 'Chassis intrusion %d detection: %s (%s)',
				$index, $status, $reading;
			report('chassis', $msg, $E_OK, $index);
		}
	}
	return;
}


#-----------------------------------------
# CHASSIS: Check ESM log
#-----------------------------------------
sub check_esmlog {
	my @output = ();

	if ($snmp) {
		my %esm_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.300.40.1.7.1' => 'eventLogSeverityStatus',
		);
		my $result = $snmp_session->get_entries(-columns => [ keys %esm_oid ]);

		# No entries is OK
		return if !defined $result;

		@output = @{get_snmp_output($result, \%esm_oid)};
		foreach my $out (@output) {
			++$count{esm}{$snmp_status{$out->{eventLogSeverityStatus}}};
		}
	}

	# Create error messages and set exit value if appropriate
	my $err = 0;
	if ($count{esm}{'Critical'} > 0) {$err = $E_CRITICAL;}
	elsif ($count{esm}{'Non-Critical'} > 0) {$err = $E_WARNING;}

	my $msg = sprintf 'ESM log content: %d critical, %d non-critical, %d ok',
		$count{esm}{'Critical'}, $count{esm}{'Non-Critical'}, $count{esm}{'Ok'};
	report('other', $msg, $err);

	return;
}

#-----------------------------------------
# CHASSIS: Check service tag
#-----------------------------------------
sub check_servicetag {
	if ($sysinfo{serial} !~ m{\A [0-9A-Z]{7} \z}xms) {
		my $msg = $sysinfo{serial} =~ m{\A \s* \z}xms
			? q{Chassis Service Tag is empty}
			: sprintf q{Chassis Service Tag is bogus: '%s'}, $sysinfo{serial};
		report('other', $msg, $E_WARNING);
	}
	else {
		my $msg = sprintf 'Chassis Service Tag is sane';
		report('other', $msg, $E_OK);
	}
	return;
}


#
# Handy function for checking all storage components
#
sub check_storage {
	check_controllers();
	check_physical_disks();
	check_virtual_disks();
	check_cache_battery();
	check_enclosures();
	check_enclosure_fans();
	check_enclosure_pwr();
	check_enclosure_temp();
	check_enclosure_emms();
	return;
}


#---------------------------------------------------------------------
# Info functions
#---------------------------------------------------------------------

#
# Fetch chassis info via SNMP, put in sysinfo hash
#
sub get_snmp_chassis_info {
	my %chassis_oid
		= (
		'1.3.6.1.4.1.674.10892.5.4.300.10.1.9.1'  => 'chassisModelName',
		'1.3.6.1.4.1.674.10892.5.4.300.10.1.11.1' => 'chassisServiceTagName',
		'1.3.6.1.4.1.674.10892.5.4.300.10.1.48.1' => 'chassisSystemRevisionName',
	);

	my $chassisInformationTable = '1.3.6.1.4.1.674.10892.5.4.300.10.1';
	my $result = $snmp_session->get_table(-baseoid => $chassisInformationTable);

	if (defined $result) {
		foreach my $oid (keys %{$result}) {
			if (exists $chassis_oid{$oid} and $chassis_oid{$oid} eq 'chassisModelName') {
				$sysinfo{model} = $result->{$oid};
				$sysinfo{model} =~ s{\s+\z}{}xms; # remove trailing whitespace
			}
			elsif (exists $chassis_oid{$oid} and $chassis_oid{$oid} eq 'chassisServiceTagName') {
				$sysinfo{serial} = $opt{hide_servicetag} ? 'XXXXXXX' : $result->{$oid};
				$sysinfo{express_sc} = POSIX::strtol($sysinfo{serial}, 36);
			}
			elsif (exists $chassis_oid{$oid} and $chassis_oid{$oid} eq 'chassisSystemRevisionName') {
				$sysinfo{rev} = q{ } . $result->{$oid};
			}
		}
	}
	else {
		my $msg = sprintf 'SNMP ERROR getting chassis info: %s',
			$snmp_session->error;
		report('other', $msg, $E_UNKNOWN);
	}
	return;
}

#
# Fetch BIOS info via SNMP, put in sysinfo hash
#
sub get_snmp_chassis_bios {
	my %bios_oid
		= (
		'1.3.6.1.4.1.674.10892.5.4.300.50.1.7.1.1' => 'systemBIOSReleaseDateName',
		'1.3.6.1.4.1.674.10892.5.4.300.50.1.8.1.1' => 'systemBIOSVersionName',
	);

	my $systemBIOSTable = '1.3.6.1.4.1.674.10892.5.4.300.50.1';
	my $result = $snmp_session->get_table(-baseoid => $systemBIOSTable);

	if (defined $result) {
		foreach my $oid (keys %{$result}) {
			if (exists $bios_oid{$oid} and $bios_oid{$oid} eq 'systemBIOSReleaseDateName') {
				$sysinfo{biosdate} = $result->{$oid};
				$sysinfo{biosdate} =~ s{\A (\d{4})(\d{2})(\d{2}).*}{$2/$3/$1}xms;
			}
			elsif (exists $bios_oid{$oid} and $bios_oid{$oid} eq 'systemBIOSVersionName') {
				$sysinfo{bios} = $result->{$oid};
			}
		}
	}
	else {
		my $msg = sprintf 'SNMP ERROR getting BIOS info: %s',
			$snmp_session->error;
		report('other', $msg, $E_UNKNOWN);
	}
	return;
}

#
# Fetch OS info via SNMP, put in sysinfo hash
#
sub get_snmp_system_operatingsystem {
	my %os_oid
		= (
		'1.3.6.1.4.1.674.10892.5.4.400.10.1.6.1' => 'operatingSystemOperatingSystemName',
		'1.3.6.1.4.1.674.10892.5.4.400.10.1.7.1' => 'operatingSystemOperatingSystemVersionName',
	);

	my $operatingSystemTable = '1.3.6.1.4.1.674.10892.5.4.400.10.1';
	my $result = $snmp_session->get_table(-baseoid => $operatingSystemTable);

	if (defined $result) {
		foreach my $oid (keys %{$result}) {
			if (exists $os_oid{$oid} and $os_oid{$oid} eq 'operatingSystemOperatingSystemName') {
				$sysinfo{osname} = ($result->{$oid});
			}
			elsif (exists $os_oid{$oid} and $os_oid{$oid} eq 'operatingSystemOperatingSystemVersionName') {
				$sysinfo{osver} = $result->{$oid};
			}
		}
	}
	else {
		my $msg = sprintf 'SNMP ERROR getting OS info: %s',
			$snmp_session->error;
		report('other', $msg, $E_UNKNOWN);
	}
	return;
}

#
# Fetch iDRAC version via SNMP, put in sysinfo hash
#
sub get_snmp_about {
	# IDRAC-MIB-SMIv2::firmwareVersionName.1.1 - usually the iDRAC - .1.2 is the Lifecycle Controller
	my $oid = '.1.3.6.1.4.1.674.10892.5.4.300.60.1.11.1.1';
	my $result = $snmp_session->get_request(-varbindlist => [ $oid ]);

	if (defined $result) {
		$sysinfo{rac_fw} = exists $result->{$oid} && $result->{$oid} ne q{}
			? $result->{$oid} : 'unknown';
	}
	else {
		my $msg = sprintf 'SNMP ERROR: Getting iDRAC version failed: %s', $snmp_session->error;
		report('other', $msg, $E_UNKNOWN);
	}
	return;
}

#
# Collects some information about the system
#
sub get_sysinfo {
	# Get system model and serial number
	get_snmp_chassis_info();

	# Get BIOS information. Only if needed
	if ($opt{okinfo} >= 1
		or $opt{debug}
		or (defined $opt{postmsg} and $opt{postmsg} =~ m/[%][bd]/xms)) {
		get_snmp_chassis_bios();
	}

	get_snmp_about();

	# Return now if debug
	return if $opt{debug};

	# Get OS information. Only if needed
	if (defined $opt{postmsg} and $opt{postmsg} =~ m/[%][or]/xms) {
		get_snmp_system_operatingsystem();
	}

	# Get hostname
	$sysinfo{hostname} = $snmp ? $opt{hostname} : hostname();

	return;
}

# Get various firmware information (BMC, RAC)
sub get_firmware_info {
	my @snmp_output = ();
	my %nrpe_output = ();

	if ($snmp) {
		my %fw_oid
			= (
			'1.3.6.1.4.1.674.10892.5.4.300.60.1.7.1'  => 'firmwareType',
			'1.3.6.1.4.1.674.10892.5.4.300.60.1.8.1'  => 'firmwareTypeName',
			'1.3.6.1.4.1.674.10892.5.4.300.60.1.11.1' => 'firmwareVersionName',
		);

		my $firmwareTable = '1.3.6.1.4.1.674.10892.5.4.300.60.1';
		my $result = $snmp_session->get_table(-baseoid => $firmwareTable);

		# Some don't have this OID, this is ok
		if (!defined $result) {
			return;
		}

		@snmp_output = @{get_snmp_output($result, \%fw_oid)};
	}

	## OK - updated for iSM
	my %fw_type # Firmware types
		= (
		1  => 'other',               # other than following values
		2  => 'unknown',             # unknown
		20 => 'lifecycleController', # Lifecycle Controller
		21 => 'iDRAC7',              # iDRAC7
		22 => 'iDRAC8',              # iDRAC8
		23 => 'iDRAC9',              # iDRAC9
	);

	if ($snmp) {
		foreach my $out (@snmp_output) {
			my $name = $out->{firmwareTypeName};
			$name =~ s/\s//gxms;
			$sysinfo{'rac'} = 1;
			$sysinfo{'rac_name'} = $name;
			$sysinfo{'rac_fw'} = $out->{firmwareVersionName};
		}
	}

	return;
}


#=====================================================================
# Main program
#=====================================================================

# Get system information
get_sysinfo();
get_firmware_info();

# Here we do the actual checking of components
# Check global status if applicable
if ($global) {
	$globalstatus = check_global();
}

# Do multiple selected checks
if ($check{storage}) {check_storage();}
if ($check{memory}) {check_memory();}
if ($check{fans}) {check_fans();}
if ($check{power}) {check_powersupplies();}
if ($check{temp}) {check_temperatures();}
if ($check{cpu}) {check_processors();}
if ($check{voltage}) {check_volts();}
if ($check{batteries}) {check_batteries();}
if ($check{amperage}) {check_pwrmonitoring();}
if ($check{intrusion}) {check_intrusion();}
if ($check{esmlog}) {check_esmlog();}
if ($check{servicetag}) {check_servicetag();}

#---------------------------------------------------------------------
# Finish up
#---------------------------------------------------------------------

# Close SNMP session
if ($snmp) {
	$snmp_session->close;
}

# Counter variable
%nagios_alert_count
	= (
	'OK'       => 0,
	'WARNING'  => 0,
	'CRITICAL' => 0,
	'UNKNOWN'  => 0,
);

# Print messages
if ($opt{debug}) {
	# finding the mode of operation
	my $mode = 'local';
	if ($snmp) {
		# Setting the domain (IP version and transport protocol)
		my $transport = $opt{tcp} ? 'TCP' : 'UDP';
		my $ipversion = $opt{ipv6} ? 'IPv6' : 'IPv4';
		$mode = "SNMPv$opt{protocol} $transport/$ipversion";
	}

	print "   System:      $sysinfo{model}$sysinfo{rev}";
	print q{ } x (25 - length "$sysinfo{model}$sysinfo{rev}"), "iDRAC version:   $sysinfo{rac_fw}\n";
	print "   ServiceTag:  $sysinfo{serial}";
	print q{ } x (25 - length $sysinfo{serial}), "Plugin version:  $VERSION\n";
	print "   BIOS/date:   $sysinfo{bios} $sysinfo{biosdate}";
	print q{ } x (25 - length "$sysinfo{bios} $sysinfo{biosdate}"), "Checking mode:   $mode\n";
	if ($#report_storage >= 0) {
		print "---------------------------------------------------------------------------------------------------------------------------------\n";
		print "   Storage Components                                                                                                            \n";
		print "=================================================================================================================================\n";
		print "  STATE  |                             ID                               |  MESSAGE TEXT                                          \n";
		print "---------+--------------------------------------------------------------+--------------------------------------------------------\n";
		foreach (@report_storage) {
			my ($msg, $level, $nexus) = @{$_};
			print q{ } x (8 - length $reverse_exitcode{$level}) . "$reverse_exitcode{$level} | "
				. q{ } x (60 - length $nexus) . "$nexus | $msg\n";
			$nagios_alert_count{$reverse_exitcode{$level}}++;
		}
	}
	if ($#report_chassis >= 0) {
		print "-----------------------------------------------------------------------------\n";
		print "   Chassis Components                                                        \n";
		print "=============================================================================\n";
		print "  STATE  |  ID  |  MESSAGE TEXT                                              \n";
		print "---------+------+------------------------------------------------------------\n";
		foreach (@report_chassis) {
			my ($msg, $level, $nexus) = @{$_};
			print q{ } x (8 - length $reverse_exitcode{$level}) . "$reverse_exitcode{$level} | "
				. q{ } x (4 - length $nexus) . "$nexus | $msg\n";
			$nagios_alert_count{$reverse_exitcode{$level}}++;
		}
	}
	if ($#report_other >= 0) {
		print "-----------------------------------------------------------------------------\n";
		print "   Other messages                                                            \n";
		print "=============================================================================\n";
		print "  STATE  |  MESSAGE TEXT                                                     \n";
		print "---------+-------------------------------------------------------------------\n";
		foreach (@report_other) {
			my ($msg, $level, $nexus) = @{$_};
			print q{ } x (8 - length $reverse_exitcode{$level}) . "$reverse_exitcode{$level} | $msg\n";
			$nagios_alert_count{$reverse_exitcode{$level}}++;
		}
	}
}
else {
	my $c = 0; # counter to determine linebreaks

	# Run through each message, sorted by severity level
	ALERT:
	foreach (sort {$a->[1] < $b->[1]} (@report_storage, @report_chassis, @report_other)) {
		my ($msg, $level, $nexus) = @{$_};
		next ALERT if $level == $E_OK;

		if (defined $opt{only}) {
			# If user wants only critical alerts
			next ALERT if ($opt{only} eq 'critical' and $level == $E_WARNING);

			# If user wants only warning alerts
			next ALERT if ($opt{only} eq 'warning' and $level == $E_CRITICAL);
		}

		# Prefix with service tag if specified with option '-i|--info'
		if ($opt{info}) {
			if (defined $opt{htmlinfo} and !$opt{hide_servicetag}) {
				$msg = '[<a target="_blank" href="' . warranty_url($sysinfo{serial})
					. "\">$sysinfo{serial}</a>] " . $msg;
			}
			else {
				$msg = "[$sysinfo{serial}] " . $msg;
			}
		}

		# Prefix with nagios level if specified with option '--state'
		$msg = $reverse_exitcode{$level} . ": $msg" if $opt{state};

		# Prefix with one-letter nagios level if specified with option '--short-state'
		$msg = (substr $reverse_exitcode{$level}, 0, 1) . ": $msg" if $opt{shortstate};

		($c++ == 0) ? print $msg : print $linebreak, $msg;

		$nagios_alert_count{$reverse_exitcode{$level}}++;
	}
}

# Determine our exit code
$exit_code = $E_OK;
$exit_code = $E_UNKNOWN if $nagios_alert_count{'UNKNOWN'} > 0;
$exit_code = $E_WARNING if $nagios_alert_count{'WARNING'} > 0;
$exit_code = $E_CRITICAL if $nagios_alert_count{'CRITICAL'} > 0;

# Global status via SNMP.. extra safety check
if ($globalstatus != $E_OK && $exit_code == $E_OK && !defined $opt{only}) {
	print "OOPS! Something is wrong with this server, but I don't know what. ";
	print "The global system health status is $reverse_exitcode{$globalstatus}, ";
	print "but every component check is OK. This may be a bug in the Nagios plugin, ";
	print "please file a bug report.\n";
	exit $E_UNKNOWN;
}

# Print OK message
if ($exit_code == $E_OK && defined $opt{only} && $opt{only} !~ m{\A critical|warning|chassis \z}xms && !$opt{debug}) {
	my %okmsg
		= ('storage' => "STORAGE OK - $count{pdisk} physical drives, $count{vdisk} logical drives",
		'fans'       => $count{fan} == 0 && $blade ? 'OK - blade system with no fan probes' : "FANS OK - $count{fan} fan probes checked",
		'temp'       => "TEMPERATURES OK - $count{temp} temperature probes checked",
		'memory'     => "MEMORY OK - $count{dimm} memory modules, $count{mem} GB total memory",
		'power'      => $count{power} == 0 ? 'OK - no instrumented power supplies found' : "POWER OK - $count{power} power supplies checked",
		'cpu'        => "PROCESSORS OK - $count{cpu} processors checked",
		'voltage'    => "VOLTAGE OK - $count{volt} voltage probes checked",
		'batteries'  => $count{bat} == 0 ? 'OK - no batteries found' : "BATTERIES OK - $count{bat} batteries checked",
		'amperage'   => $count{amp} == 0 ? 'OK - no power monitoring probes found' : "AMPERAGE OK - $count{amp} amperage (power monitoring) probes checked",
		'intrusion'  => $count{intr} == 0 ? 'OK - no intrusion detection probes found' : "INTRUSION OK - $count{intr} intrusion detection probes checked",
		'alertlog'   => $snmp ? 'OK - not supported via snmp' : "OK - Alert Log content: $count{alert}{Ok} ok, $count{alert}{'Non-Critical'} warning and $count{alert}{Critical} critical",
		'esmlog'     => "OK - ESM Log content: $count{esm}{Ok} ok, $count{esm}{'Non-Critical'} warning and $count{esm}{Critical} critical",
		'sdcard'     => "SD CARDS OK - $count{sd} SD cards installed",
		'servicetag' => sprintf 'ServiceTag OK: %s', $opt{hide_servicetag} ? 'XXXXXXX' : $sysinfo{serial},
	);

	print $okmsg{$opt{only}};

	# show blacklisted components
	if ($opt{show_blacklist} and %blacklist) {
		my @blstr = ();
		foreach (keys %blacklist) {
			push @blstr, "$_=" . join ',', @{$blacklist{$_}};
		}
		print $linebreak;
		print "----- BLACKLISTED: " . join '/', @blstr;
	}
}
elsif ($exit_code == $E_OK && !$opt{debug}) {
	if (defined $opt{htmlinfo} and !$opt{hide_servicetag}) {
		printf q{OK - System: '<a target="_blank" href="%s">%s%s</a>', SN: '<a target="_blank" href="%s">%s</a>'},
			documentation_url($sysinfo{model}, $sysinfo{rev}), $sysinfo{model}, $sysinfo{rev},
			warranty_url($sysinfo{serial}), $sysinfo{serial};
	}
	elsif (defined $opt{htmlinfo} and $opt{hide_servicetag}) {
		printf q{OK - System: '<a target="_blank" href="%s">%s%s</a>', SN: '%s'},
			documentation_url($sysinfo{model}, $sysinfo{rev}), $sysinfo{model}, $sysinfo{rev},
			$sysinfo{serial};
	}
	else {
		printf q{OK - System: '%s%s', SN: '%s'},
			$sysinfo{model}, $sysinfo{rev}, $sysinfo{serial};
	}

	if ($check{memory}) {
		my $unit = 'MB';
		if ($count{mem} >= 1) {
			$count{mem} /= 1;
			$unit = 'GB';
		}
		printf ', %d %s ram (%d dimms)', $count{mem}, $unit, $count{dimm};
	}
	else {
		print ', not checking memory';
	}

	if ($check{storage}) {
		printf ', %d logical drives, %d physical drives',
			$count{vdisk}, $count{pdisk};
	}
	else {
		print ', not checking storage';
	}

	# show blacklisted components
	if ($opt{show_blacklist} and %blacklist) {
		my @blstr = ();
		foreach (keys %blacklist) {
			push @blstr, "$_=" . join ',', @{$blacklist{$_}};
		}
		print $linebreak;
		print "----- BLACKLISTED: " . join '/', @blstr;
	}

	if ($opt{okinfo} >= 1) {
		print $linebreak;
		printf q{----- BIOS='%s %s'}, $sysinfo{bios}, $sysinfo{biosdate};

		if ($sysinfo{rac}) {
			printf q{, %s='%s'}, $sysinfo{rac_name}, $sysinfo{rac_fw};
		}
	}

	if ($opt{okinfo} >= 2) {
		if ($check{storage}) {
			my @storageprint = ();
			foreach my $id (sort keys %{$sysinfo{controller}}) {
				chomp $sysinfo{controller}{$id}{driver};
				my $msg = sprintf q{----- Ctrl %s [%s]: Fw='%s', Dr='%s'},
					$sysinfo{controller}{$id}{id}, $sysinfo{controller}{$id}{name},
					$sysinfo{controller}{$id}{firmware}, $sysinfo{controller}{$id}{driver};
				if (defined $sysinfo{controller}{$id}{storport}) {
					$msg .= sprintf q{, Storport: '%s'}, $sysinfo{controller}{$id}{storport};
				}
				push @storageprint, $msg;
			}
			foreach my $id (sort keys %{$sysinfo{enclosure}}) {
				push @storageprint, sprintf q{----- Encl %s [%s]: Fw='%s'},
					$sysinfo{enclosure}{$id}->{id}, $sysinfo{enclosure}{$id}->{name},
					$sysinfo{enclosure}{$id}->{firmware};
			}

			# print stuff
			foreach my $line (@storageprint) {
				print $linebreak, $line;
			}
		}
	}

}
else {
	if ($opt{extinfo}) {
		print $linebreak;
		if (defined $opt{htmlinfo} && !$opt{hide_servicetag}) {
			printf '------ SYSTEM: <a target="_blank" href="%s">%s%s</a>, SN: <a target="_blank" href="%s">%s</a>',
				documentation_url($sysinfo{model}), $sysinfo{model}, $sysinfo{rev},
				warranty_url($sysinfo{serial}), $sysinfo{serial};
		}
		elsif (defined $opt{htmlinfo} && $opt{hide_servicetag}) {
			printf '------ SYSTEM: <a target="_blank" href="%s">%s%s</a>, SN: %s',
				documentation_url($sysinfo{model}), $sysinfo{model}, $sysinfo{rev},
				$sysinfo{serial};
		}
		else {
			printf '------ SYSTEM: %s%s, SN: %s',
				$sysinfo{model}, $sysinfo{rev}, $sysinfo{serial};
		}
	}
	if (defined $opt{postmsg}) {
		my $post = undef;
		if (-f $opt{postmsg}) {
			open my $POST, '<', $opt{postmsg}
				or (print $linebreak
				and print "ERROR: Couldn't open post message file $opt{postmsg}: $!\n"
				and exit $E_UNKNOWN);
			$post = <$POST>;
			close $POST;
			chomp $post;
		}
		else {
			$post = $opt{postmsg};
		}
		if (defined $post) {
			print $linebreak;
			$post =~ s{[%]h}{$sysinfo{hostname}}gxms;
			$post =~ s{[%]e}{$sysinfo{express_sc}}gxms;
			$post =~ s{[%]s}{$sysinfo{serial}}gxms;
			$post =~ s{[%]m}{$sysinfo{model}$sysinfo{rev}}gxms;
			$post =~ s{[%]b}{$sysinfo{bios}}gxms;
			$post =~ s{[%]d}{$sysinfo{biosdate}}gxms;
			$post =~ s{[%]o}{$sysinfo{osname}}gxms;
			$post =~ s{[%]r}{$sysinfo{osver}}gxms;
			$post =~ s{[%]p}{$count{pdisk}}gxms;
			$post =~ s{[%]l}{$count{vdisk}}gxms;
			$post =~ s{[%]n}{$linebreak}gxms;
			$post =~ s{[%]{2}}{%}gxms;
			print $post;
		}
	}
}

# Reset the WARN signal
$SIG{__WARN__} = 'DEFAULT';

# Print any perl warnings that have occured
if (@perl_warnings) {
	foreach (@perl_warnings) {
		chop @$_;
		print "${linebreak}INTERNAL ERROR: @$_";
	}
	$exit_code = $E_UNKNOWN;
}

# Print performance data
if (defined $opt{perfdata} && !$opt{debug} && @perfdata) {
	my $lb = $opt{perfdata} eq 'multiline' ? "\n" : q{ }; # line break for perfdata
	print q{|};

	# Sort routine for performance data
	sub perfsort {
		my %order = ('T' => 0, 'W' => 1, 'A' => 2, 'V' => 3, 'F' => 4, 'E' => 5,);

		# sort in this order:
		#  1. the type according to the hash "order" above
		#  2. the id (index) numerically
		#  3. the id (index) alphabetically
		#  4. the label
		return $order{$a->{type}} cmp $order{$b->{type}} ||
			($a->{id} =~ m{\A\d+\z}xms and $a->{id} <=> $b->{id}) ||
			($a->{id} !~ m{\A\d+\z}xms and $a->{id} cmp $b->{id}) ||
			$a->{label} cmp $b->{label};
	}

	# LEGACY sort routine for performance data
	sub perfsort_legacy {
		my %order = (fan => 0, pwr => 1, tem => 2, enc => 3,);
		return ($order{(substr $a->{legacy}, 0, 3)} cmp $order{(substr $b->{legacy}, 0, 3)}) ||
			$a->{legacy} cmp $b->{legacy};
	}

	# Print performance data sorted
	if ($opt{legacy_perfdata}) {
		my $type = $opt{perfdata} eq 'minimal' ? 'mini' : 'legacy';
		print join $lb, map {"$_->{$type}=$_->{value};$_->{warn};$_->{crit}"} sort perfsort_legacy @perfdata;
	}
	else {
		if ($opt{perfdata} eq 'minimal') {
			print join $lb, map {"$_->{type}$_->{id}=$_->{value}$_->{unit};$_->{warn};$_->{crit}"} sort perfsort @perfdata;
		}
		else {
			print join $lb, map {"$_->{type}$_->{id}_$_->{label}=$_->{value}$_->{unit};$_->{warn};$_->{crit}"} sort perfsort @perfdata;
		}
	}
}

# Wrapping up and finishing
if ($opt{debug}) {
	# Exit with value 3 (unknown) if debug
	exit $E_UNKNOWN;
}
else {
	# Print a linebreak at the end if we have a TTY
	isatty(*STDOUT) && print "\n";

	# Exit with proper exit code
	exit $exit_code;
}