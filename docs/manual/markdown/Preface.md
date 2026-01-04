# Preface

The *Lustre^\*^Software Release 2.x Operations Manual* provides detailed
information and procedures to install, configure and tune a Lustre file
system. The manual covers topics such as failover, quotas, striping, and
bonding. This manual also contains troubleshooting information and tips
to improve the operation and performance of a Lustre file system.

# About this Document

This document is maintained by Whamcloud in Docbook format. The
canonical version is available at [
https://wiki.whamcloud.com/display/PUB/Documentation
](https://wiki.whamcloud.com/display/PUB/Documentation).

## UNIX^\*^ Commands

This document does not contain information about basic UNIX^\*^
operating system commands and procedures such as shutting down the
system, booting the system, and configuring devices. Refer to the
following for this information:

-   Software documentation that you received with your system

-   Red Hat^\*^ Enterprise Linux^\*^ documentation, which is at: [
    https://docs.redhat.com/docs/en-US/index.html](https://docs.redhat.com/docs/en-US/index.html)

    ::: note
    The Lustre client module is available for many different Linux^\*^
    versions and distributions. The Red Hat Enterprise Linux
    distribution is the best supported and tested platform for Lustre
    servers.
    :::

## Shell Prompts

The shell prompt used in the example text indicates whether a command
can or should be executed by a regular user, or whether it requires
superuser permission to run. Also, the machine type is often included in
the prompt to indicate whether the command should be run on a client
node, on an MDS node, an OSS node, or the MGS node.

Some examples are listed below, but other prompt combinations are also
used as needed for the example.

+-----------------------------------+-----------------------------------+
| **Shell**                         | **Prompt**                        |
+===================================+===================================+
| Regular user                      | `machine$`                        |
+-----------------------------------+-----------------------------------+
| Superuser (root)                  | `machine#`                        |
+-----------------------------------+-----------------------------------+
| Regular user on the client        | `client$`                         |
+-----------------------------------+-----------------------------------+
| Superuser on the MDS              | `mds#`                            |
+-----------------------------------+-----------------------------------+
| Superuser on the OSS              | `oss#`                            |
+-----------------------------------+-----------------------------------+
| Superuser on the MGS              | `mgs#`                            |
+-----------------------------------+-----------------------------------+

## Related Documentation

+-----------------+-----------------+---------+------------------------+
| **Application** | **Title**       | **F     | **Location**           |
|                 |                 | ormat** |                        |
+=================+=================+=========+========================+
| Latest          | *Lustre         | Wiki    | Online at              |
| information     | Software        | page    | <https://w             |
|                 | Release 2.x     |         | iki.whamcloud.com/disp |
|                 | Change Logs*    |         | lay/PUB/Documentation> |
+-----------------+-----------------+---------+------------------------+
| Service         | *Lustre         | PDF     | Online at              |
|                 | Software        |         | <https://w             |
|                 | Release 2.x     | HTML    | iki.whamcloud.com/disp |
|                 | Operations      |         | lay/PUB/Documentation> |
|                 | Manual*         |         |                        |
+-----------------+-----------------+---------+------------------------+

## Documentation and Support

These web sites provide additional resources:

-   Documentation [
    https://wiki.whamcloud.com/display/PUB/Documentation](https://wiki.whamcloud.com/display/PUB/Documentation)
    <https://www.lustre.org>

-   Support <https://jira.whamcloud.com/>
